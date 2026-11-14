use rex_cedar_auth::cedar_auth::CedarAuth;
use rex_cedar_auth::fs::actions::FilesystemAction;
use rex_cedar_auth::fs::entities::FileEntity;

use cap_fs_ext::{DirExt, SystemTimeSpec as CapSystemTimeSpec};
use cap_std::fs::PermissionsExt;
use cap_std::time::SystemTime;
use cap_tempfile::TempFile;
use flate2::read::GzDecoder;
use fs_set_times::{SetTimes, SystemTimeSpec};
use std::io::{self, copy};
use std::io::{ErrorKind, Read};
use std::path::PathBuf;
use std::time::{Duration, UNIX_EPOCH};
use tar::Archive;

use rex_logger::{debug, warn};

use crate::constants::error_constants::{
    ARCHIVE_ENTRY_COUNT_LIMIT_EXCEEDED_ERR, ARCHIVE_ENTRY_SIZE_LIMIT_EXCEEDED_ERR,
    ARCHIVE_ENTRY_SIZE_MISMATCH_ERR, ARCHIVE_TOTAL_SIZE_LIMIT_EXCEEDED_ERR,
};
use crate::errors::RustSafeIoError;
use crate::options::{ChmodDirOptions, ExtractArchiveOptions, SetOwnershipOptions};
use crate::{RcDirHandle, RcFileHandle, build_path, is_authorized, set_ownership_inner};

/// Extraction budgets validated before and enforced during archive extraction.
///
/// All limits are optional; `None` disables the corresponding check.
#[derive(Debug, Clone, Copy, Default)]
struct ExtractionBudget {
    /// Maximum total uncompressed bytes of regular file entries.
    max_total_bytes: Option<u64>,
    /// Maximum uncompressed size of a single regular file entry.
    max_entry_bytes: Option<u64>,
    /// Maximum number of entries of any type in the archive.
    max_entry_count: Option<u64>,
    /// Number of entries already seen in the archive.
    entry_count: u64,
    /// Uncompressed bytes already streamed for regular file entries.
    total_consumed: u64,
}

impl ExtractionBudget {
    fn from_options(options: ExtractArchiveOptions) -> Self {
        Self {
            max_total_bytes: options.max_extracted_bytes,
            max_entry_bytes: options.max_entry_size_bytes,
            max_entry_count: options.max_entry_count,
            entry_count: 0,
            total_consumed: 0,
        }
    }

    /// Accounts for one archive entry of any type and enforces the entry count limit.
    ///
    /// Called before the entry is processed so count violations fail before any destination
    /// write associated with the offending entry.
    fn count_entry(&mut self, path: &str) -> Result<(), RustSafeIoError> {
        self.entry_count = self.entry_count.saturating_add(1);
        if let Some(limit) = self.max_entry_count
            && self.entry_count > limit
        {
            return Err(RustSafeIoError::ArchiveBudgetExceededError {
                reason: format!(
                    "{ARCHIVE_ENTRY_COUNT_LIMIT_EXCEEDED_ERR}: limit is {limit} entries"
                ),
                path: Some(PathBuf::from(path)),
            });
        }
        Ok(())
    }

    /// Validates the header-declared size of a regular entry against the per-entry and cumulative
    /// budgets before any of its payload is written.
    fn check_declared_size(&mut self, path: &str, entry_size: u64) -> Result<(), RustSafeIoError> {
        if let Some(limit) = self.max_entry_bytes
            && entry_size > limit
        {
            return Err(RustSafeIoError::ArchiveBudgetExceededError {
                reason: format!(
                    "{ARCHIVE_ENTRY_SIZE_LIMIT_EXCEEDED_ERR}: entry '{path}' is {entry_size} bytes, limit is {limit} bytes"
                ),
                path: Some(PathBuf::from(path)),
            });
        }

        let projected_total = self.total_consumed.saturating_add(entry_size);
        if let Some(limit) = self.max_total_bytes
            && projected_total > limit
        {
            return Err(RustSafeIoError::ArchiveBudgetExceededError {
                reason: format!(
                    "{ARCHIVE_TOTAL_SIZE_LIMIT_EXCEEDED_ERR}: archive would extract {projected_total} regular file bytes, limit is {limit} bytes"
                ),
                path: Some(PathBuf::from(path)),
            });
        }

        Ok(())
    }

    /// Records the number of payload bytes actually streamed for a regular entry.
    fn add_consumed_bytes(&mut self, bytes: u64) {
        self.total_consumed = self.total_consumed.saturating_add(bytes);
    }
}

/// Reader wrapper that enforces the per-entry and cumulative byte budgets while streaming.
///
/// The extraction loop already validates the sizes declared in the tar headers; this wrapper is
/// a defense-in-depth check against entries whose actual payload is longer than their header
/// claims. It stops reading as soon as the header size or either budget would be exceeded instead
/// of letting a malicious archive fill the working directory.
struct BudgetedReader<R: Read> {
    inner: R,
    entry_path: String,
    /// Bytes still allowed by the entry's own tar header; reads past it mean a malformed archive.
    declared_remaining: u64,
    /// Configured per-entry size limit.
    entry_limit: Option<u64>,
    /// Bytes already streamed for this entry.
    entry_consumed: u64,
    /// Configured cumulative size limit across all regular entries.
    total_limit: Option<u64>,
    /// Cumulative regular-entry bytes streamed by the archive so far, including this reader.
    total_consumed: u64,
    /// Bytes streamed through this reader since it was created.
    self_consumed: u64,
}

impl<R: Read> BudgetedReader<R> {
    fn new(
        inner: R,
        entry_path: &str,
        declared_size: u64,
        entry_limit: Option<u64>,
        total_limit: Option<u64>,
        total_consumed: u64,
    ) -> Self {
        Self {
            inner,
            entry_path: entry_path.to_string(),
            declared_remaining: declared_size,
            entry_limit,
            entry_consumed: 0,
            total_limit,
            total_consumed,
            self_consumed: 0,
        }
    }

    fn exceeded_error(&self, limit_kind: &str, limit: u64, actual: u64) -> io::Error {
        io::Error::new(
            ErrorKind::InvalidData,
            RustSafeIoError::ArchiveBudgetExceededError {
                reason: format!(
                    "{limit_kind}: entry '{}' reached {actual} bytes, limit is {limit} bytes",
                    self.entry_path
                ),
                path: Some(PathBuf::from(&self.entry_path)),
            },
        )
    }

    fn mismatch_error(&self) -> io::Error {
        io::Error::new(
            ErrorKind::InvalidData,
            RustSafeIoError::ArchiveBudgetExceededError {
                reason: format!(
                    "{ARCHIVE_ENTRY_SIZE_MISMATCH_ERR}: entry '{}' produced more bytes than its tar header declares",
                    self.entry_path
                ),
                path: Some(PathBuf::from(&self.entry_path)),
            },
        )
    }

    /// Bytes read through this reader since it was created.
    fn bytes_read(&self) -> u64 {
        self.self_consumed
    }
}

impl<R: Read> Read for BudgetedReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let written = self.inner.read(buf)?;
        let written_u64 = u64::try_from(written).unwrap_or(u64::MAX);

        if written_u64 > self.declared_remaining {
            return Err(self.mismatch_error());
        }
        self.declared_remaining = self.declared_remaining.saturating_sub(written_u64);

        self.entry_consumed = self.entry_consumed.saturating_add(written_u64);
        if let Some(limit) = self.entry_limit
            && self.entry_consumed > limit
        {
            return Err(self.exceeded_error(
                ARCHIVE_ENTRY_SIZE_LIMIT_EXCEEDED_ERR,
                limit,
                self.entry_consumed,
            ));
        }

        self.self_consumed = self.self_consumed.saturating_add(written_u64);
        self.total_consumed = self.total_consumed.saturating_add(written_u64);
        if let Some(limit) = self.total_limit
            && self.total_consumed > limit
        {
            return Err(self.exceeded_error(
                ARCHIVE_TOTAL_SIZE_LIMIT_EXCEEDED_ERR,
                limit,
                self.total_consumed,
            ));
        }

        Ok(written)
    }
}

impl RcFileHandle {
    /// Extracts a tar.gz archive to a destination directory with Cedar authorization.
    ///
    /// This method safety extracts archive contents with comprehensive security checks:
    /// - Cedar authorization for each extracted file and directory
    /// - Skips special file types (symlinks, devices, etc.)
    /// - Configurable extraction budgets (total bytes, single entry bytes, entry count) that fail the
    ///   whole operation with [`RustSafeIoError::ArchiveBudgetExceededError`] before any destination
    ///   path is created or overwritten
    /// - Optional preservation of permissions, ownership, and timestamps (see [`ExtractArchiveOptions`] for defaults)
    ///   - Permissions: preserved by default, when disabled files use system default permissions
    ///   - Ownership: not preserved by default, when enabled attempts to maintain original ownership (requires elevated privileges)
    ///   - Timestamps: preserved by default, when disabled files use current extraction time
    /// - Best effort approach for per-entry authorization and metadata errors, it continues processing
    ///   extraction even after encountering them, while budget violations, malformed archives and I/O
    ///   errors fail the whole operation
    ///
    /// # Failure strategy
    ///
    /// Every budget is checked from the entry header before that entry creates any parent
    /// directory, temporary file or destination path, and a streaming reader enforces the same
    /// limits against the actual payload. A budget violation, malformed archive or I/O error fails
    /// the whole operation and triggers a rollback that removes every path this extraction
    /// created; paths that already existed beforehand are left in place. Each regular file is
    /// still written through a temporary file and atomically renamed into place, so no partial
    /// file is ever visible.
    ///
    /// Only supported for Unix-based platforms due to permission and ownership handling requirements.
    ///
    /// # Arguments
    ///
    /// * `cedar_auth` - The Cedar authorization instance
    /// * `dest_dir` - The destination directory handle where archive contents will be extracted
    /// * `options` - [`ExtractArchiveOptions`] controlling extraction behavior
    ///
    /// # Returns
    ///
    /// * `Result<()>`
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// * The principal doesn't have permission to read the archive file
    /// * The principal doesn't have permission to create files/directories in the destination
    /// * The principal doesn't have permission to write files in the destination
    /// * A configured extraction budget (total bytes, entry size or entry count) is exceeded
    /// * The archive file is corrupted or cannot be read
    /// * The archive file was not opened with read open options
    /// * Any I/O errors occur during extraction
    ///
    /// # Logging
    ///
    /// This method provides detailed logging:
    /// - Debug messages for successfully extracted files and directories
    /// - Warning messages for failed extractions (extraction continues)
    /// - Info messages for skipped special file types
    ///
    /// # Example
    ///
    /// ```no_run
    /// use rust_safe_io::DirConfigBuilder;
    /// use rust_safe_io::options::{OpenDirOptionsBuilder, OpenFileOptionsBuilder, ExtractArchiveOptionsBuilder};
    /// # use rex_cedar_auth::test_utils::{get_default_test_rex_policy, get_default_test_rex_schema};
    /// # use rex_cedar_auth::cedar_auth::CedarAuth;
    /// #
    /// # let cedar_auth = CedarAuth::new(
    /// #     &get_default_test_rex_policy(),
    /// #     get_default_test_rex_schema(),
    /// #     "[]"
    /// # ).unwrap().0;
    ///
    /// let source_dir = DirConfigBuilder::default()
    ///     .path("/tmp/source".to_string())
    ///     .build().unwrap()
    ///     .safe_open(&cedar_auth, OpenDirOptionsBuilder::default().build().unwrap())
    ///     .unwrap();
    ///
    /// let dest_dir = DirConfigBuilder::default()
    ///     .path("/tmp/dest".to_string())
    ///     .build().unwrap()
    ///     .safe_open(&cedar_auth, OpenDirOptionsBuilder::default().create(true).build().unwrap())
    ///     .unwrap();
    ///
    /// let archive_handle = source_dir.safe_open_file(
    ///     &cedar_auth,
    ///     "archive.tar.gz",
    ///     OpenFileOptionsBuilder::default().read(true).build().unwrap()
    /// ).unwrap();
    ///
    /// let options = ExtractArchiveOptionsBuilder::default()
    ///     .preserve_permissions(true)
    ///     .preserve_ownership(true)
    ///     .preserve_timestamps(true)
    ///     .build().unwrap();
    ///
    /// archive_handle.safe_extract_archive(&cedar_auth, dest_dir, options).unwrap();
    /// ```
    #[allow(clippy::needless_pass_by_value)]
    pub fn safe_extract_archive(
        &self,
        cedar_auth: &CedarAuth,
        dest_dir: RcDirHandle,
        options: ExtractArchiveOptions,
    ) -> Result<(), RustSafeIoError> {
        self.validate_read_open_option(cedar_auth)?;

        let budget = ExtractionBudget::from_options(options);

        // Snapshot the top-level destination entries so a fatal failure can roll back every path
        // this extraction created without touching anything that existed beforehand.
        let preexisting_entries = snapshot_top_level_entries(&dest_dir)?;

        let extraction =
            self.extract_archive_entries(cedar_auth, dest_dir.clone(), options, budget);

        if let Err(extract_error) = extraction {
            warn!("Archive extraction failed, rolling back partial extraction: {extract_error}");
            rollback_extracted_entries(&dest_dir, &preexisting_entries);
            return Err(extract_error);
        }

        Ok(())
    }
}

/// Lists the top-level entry names currently present in the destination directory.
fn snapshot_top_level_entries(dest_dir: &RcDirHandle) -> Result<Vec<String>, RustSafeIoError> {
    let mut names = Vec::new();
    for entry in dest_dir.dir_handle.dir.entries()? {
        let entry = entry?;
        names.push(entry.file_name().to_string_lossy().to_string());
    }
    Ok(names)
}

/// Removes every top-level entry the extraction created, leaving pre-existing entries untouched.
///
/// Rollback failures are only logged: the original extraction error remains the one reported to
/// the caller, and the cap-std sandbox guarantees the removal targets stay inside the destination.
fn rollback_extracted_entries(dest_dir: &RcDirHandle, preexisting_entries: &[String]) {
    let current_entries = match snapshot_top_level_entries(dest_dir) {
        Ok(entries) => entries,
        Err(error) => {
            warn!("Could not list destination entries during rollback: {error}");
            return;
        }
    };

    for name in current_entries {
        if preexisting_entries.contains(&name) {
            continue;
        }

        let remove_result = dest_dir
            .dir_handle
            .dir
            .remove_dir_all(&name)
            .or_else(|_| dest_dir.dir_handle.dir.remove_file(&name));

        if let Err(error) = remove_result {
            warn!("Could not remove extracted entry '{name}' during rollback: {error}");
        }
    }
}

impl RcFileHandle {
    /// Streams every archive entry into the destination directory, enforcing the budget while
    /// reading file payloads.
    #[allow(clippy::needless_pass_by_value)]
    fn extract_archive_entries(
        &self,
        cedar_auth: &CedarAuth,
        dest_dir: RcDirHandle,
        options: ExtractArchiveOptions,
        mut budget: ExtractionBudget,
    ) -> Result<(), RustSafeIoError> {
        let file_clone = self.file_handle.file.try_clone()?;
        let reader: Box<dyn Read> = Box::new(GzDecoder::new(file_clone));
        let mut archive = Archive::new(reader);

        let mut directories = Vec::new();
        for entry_result in archive.entries()? {
            let mut entry = entry_result?;
            let path = entry.path()?;
            let header = entry.header();
            let path_str = path.to_string_lossy().to_string();
            let entry_size = header.size()?;

            // Count first so the entry limit trips before the entry can create any path.
            budget.count_entry(&path_str)?;

            match header.entry_type() {
                tar::EntryType::Directory => {
                    directories.push((path_str, header.clone()));
                }
                tar::EntryType::Regular => {
                    // Header-based budget check happens before parent directories or the
                    // temporary file are created, so oversized entries leave no artifacts.
                    budget.check_declared_size(&path_str, entry_size)?;

                    let entry_header = header.clone();
                    let mut budgeted_reader = BudgetedReader::new(
                        &mut entry,
                        &path_str,
                        entry_size,
                        budget.max_entry_bytes,
                        budget.max_total_bytes,
                        budget.total_consumed,
                    );
                    match extract_archive_file(
                        cedar_auth,
                        dest_dir.clone(),
                        &path_str,
                        &entry_header,
                        budgeted_reader.by_ref(),
                        options,
                    ) {
                        Ok(()) => {
                            budget.add_consumed_bytes(budgeted_reader.bytes_read());
                            debug!("Extracted file: {path_str}");
                        }
                        Err(e)
                            if matches!(e, RustSafeIoError::ArchiveBudgetExceededError { .. }) =>
                        {
                            return Err(e);
                        }
                        Err(e) => {
                            warn!("Failed to extract file {path_str}: {e}");
                        }
                    }
                }
                _ => {
                    debug!(
                        "Skipping entry type {:?}: {}",
                        header.entry_type(),
                        path.display()
                    );
                }
            }
        }

        // Sort directories by depth (deepest first) to avoid permission conflicts when applying restrictive permissions to parent directories
        directories.sort_by(|a, b| b.0.cmp(&a.0));

        // Apply directory metadata after all files are extracted to ensure each directory gets its preserved attributes from the tar archive
        for (path_str, header) in directories {
            match apply_archive_directory_attributes(
                cedar_auth,
                dest_dir.clone(),
                &path_str,
                &header,
                options,
            ) {
                Ok(()) => {}
                Err(e) => {
                    warn!("Failed to apply directory attributes {path_str}: {e}");
                }
            }
        }

        Ok(())
    }
}

/// Creates directory path and applies tar archive metadata to the target directory.
///
/// This function is called during tar extraction to recreate directory structure
/// with preserved attributes. It ensures the full directory path exists, then applies
/// preservation settings (permissions, ownership, timestamps) only to the final
/// directory specified by `path`. Any intermediate directories created get default
/// system attributes.
///
/// Only supported for Unix-based platforms due to permission and ownership handling requirements.
///
/// # Arguments
///
/// * `cedar_auth` - The Cedar authorization instance
/// * `dest_dir` - The destination directory handle where the directory will be created
/// * `path` - The relative path of the directory to create within the destination
/// * `header` - The tar header containing directory metadata
/// * `options` - [`ExtractArchiveOptions`] controlling extraction behavior
///
/// # Returns
///
/// * `Result<()>`
///
/// # Errors
///
/// Returns an error if:
/// * The principal doesn't have permission to create the directory
/// * Directory creation fails due to I/O errors
///
/// Permission, ownership, and timestamp preservation failures are logged as warnings but do not cause errors.
#[allow(clippy::needless_pass_by_value)]
fn apply_archive_directory_attributes(
    cedar_auth: &CedarAuth,
    dest_dir: RcDirHandle,
    path: &str,
    header: &tar::Header,
    options: ExtractArchiveOptions,
) -> Result<(), RustSafeIoError> {
    dest_dir.safe_create_sub_directories(cedar_auth, path)?;

    let dir_handle = if let Ok(handle) = dest_dir.safe_open_subdir(cedar_auth, path) {
        handle
    } else {
        let mut current_dir = dest_dir;
        for component in path.split('/').filter(|c| !c.is_empty()) {
            current_dir = current_dir.safe_open_subdir(cedar_auth, component)?;
        }
        current_dir
    };

    if options.preserve_permissions {
        let mode = header.mode()?;
        match dir_handle.safe_chmod(
            cedar_auth,
            ChmodDirOptions {
                permissions: i64::from(mode),
                recursive: false,
            },
        ) {
            Ok(()) => {}
            Err(e) => {
                warn!("Could not set permissions for directory {path}: {e}");
            }
        }
    }

    if options.preserve_ownership {
        let username = header.username()?.map(ToString::to_string);
        let groupname = header.groupname()?.map(ToString::to_string);

        match dir_handle.set_ownership(
            cedar_auth,
            SetOwnershipOptions {
                user: username,
                group: groupname,
                recursive: false,
            },
        ) {
            Ok(()) => {}
            Err(e) => {
                warn!("Could not preserve ownership for directory {path}: {e}");
            }
        }
    }

    if options.preserve_timestamps {
        let mtime = header.mtime()?;
        let std_time = UNIX_EPOCH + Duration::from_secs(mtime);
        let cap_time = SystemTime::from_std(std_time);
        let mtime_spec = CapSystemTimeSpec::from(cap_time);

        if let Err(e) = DirExt::set_times(&dir_handle.dir_handle.dir, ".", None, Some(mtime_spec)) {
            warn!("Could not preserve timestamps for directory {path}: {e}");
        }
    }

    Ok(())
}

/// Extracts a regular file entry from a tar archive with Cedar authorization and metadata preservation.
///
/// This internal function handles the extraction of regular file entries from tar archives,
/// including atomic file creation using temporary files and optional preservation of
/// permissions, ownership, and timestamps based on the provided options.
///
/// Only supported for Unix-based platforms due to permission and ownership handling requirements.
///
/// # Arguments
///
/// * `cedar_auth` - The Cedar authorization instance
/// * `dest_dir` - The destination directory handle where the file will be created
/// * `path` - The relative path of the file to create within the destination
/// * `header` - The tar header containing the entry metadata
/// * `reader` - The budget-enforcing reader streaming the file payload
/// * `options` - [`ExtractArchiveOptions`] controlling extraction behavior
///
/// # Returns
///
/// * `Result<()>` - Success or error
///
/// # Errors
///
/// Returns an error if:
/// * The principal doesn't have permission to create the file
/// * File creation or data copying fails due to I/O errors
/// * Permission, ownership, or timestamp preservation fails (logged as warnings)
#[allow(clippy::needless_pass_by_value)]
fn extract_archive_file(
    cedar_auth: &CedarAuth,
    dest_dir: RcDirHandle,
    path: &str,
    header: &tar::Header,
    reader: &mut BudgetedReader<&mut tar::Entry<Box<dyn Read>>>,
    options: ExtractArchiveOptions,
) -> Result<(), RustSafeIoError> {
    let full_path = build_path(&dest_dir.dir_handle.dir_config.path, path);
    let file_entity = &FileEntity::from_string_path(&full_path)?;

    is_authorized(cedar_auth, &FilesystemAction::Create, file_entity)?;
    is_authorized(cedar_auth, &FilesystemAction::Write, file_entity)?;

    if let Some(last_slash) = path.rfind('/') {
        let parent_path = &path[..last_slash];
        dest_dir.safe_create_sub_directories(cedar_auth, parent_path)?;
    }

    let temp_file = TempFile::new(&dest_dir.dir_handle.dir)?;

    copy(reader, &mut temp_file.as_file())?;

    if options.preserve_permissions {
        let result = is_authorized(cedar_auth, &FilesystemAction::Chmod, file_entity)
            .and_then(|()| header.mode().map_err(Into::into))
            .and_then(|mode| {
                let permissions = PermissionsExt::from_mode(mode);
                temp_file
                    .as_file()
                    .set_permissions(permissions)
                    .map_err(Into::into)
            });

        if let Err(e) = result {
            warn!("Could not set permissions for file {path}: {e}");
        }
    }

    if options.preserve_ownership {
        let result =
            is_authorized(cedar_auth, &FilesystemAction::Chown, file_entity).and_then(|()| {
                let username = header.username()?.map(ToString::to_string);
                let groupname = header.groupname()?.map(ToString::to_string);
                set_ownership_inner(temp_file.as_file(), username, groupname)
            });

        if let Err(e) = result {
            warn!("Could not preserve ownership for file {path}: {e}");
        }
    }

    if options.preserve_timestamps {
        let mtime = header.mtime()?;
        let mtime_spec = SystemTimeSpec::from(UNIX_EPOCH + Duration::from_secs(mtime));
        temp_file.as_file().set_times(None, Some(mtime_spec))?;
    }

    temp_file.as_file().sync_all()?;
    temp_file.replace(path)?;

    Ok(())
}
