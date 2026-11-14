use crate::test_common::open_test_dir_handle;
use rex_cedar_auth::fs::actions::FilesystemAction;
use rex_cedar_auth::test_utils::{
    DEFAULT_TEST_CEDAR_AUTH, TestCedarAuthBuilder, get_test_rex_principal,
};
use rex_test_utils::assertions::assert_error_contains;
use rex_test_utils::io::{ArchiveEntry, create_temp_dir_and_path, create_test_archive};

use anyhow::Result;
use assert_fs::fixture::PathChild;
use assert_fs::fixture::{FileWriteStr, PathCreateDir};
use flate2::{Compression, write::GzEncoder};
use rstest::rstest;
use rust_safe_io::error_constants::READ_FILE_FLAG_ERR;
use rust_safe_io::options::{ExtractArchiveOptionsBuilder, OpenFileOptionsBuilder};
use std::fs::File;
use std::fs::Permissions;
use std::fs::set_permissions;
use std::fs::{metadata, read_dir, read_to_string};
use std::io::Write;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::Path;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tar::{Builder as TarBuilder, Header as TarHeader};
use tracing::Level;
use tracing_subscriber::fmt;

const PERMISSION_EXTRACT_BITMASK: u32 = 0o777;

/// Creates a tar.gz archive containing a regular entry whose header declares a huge size while
/// only a small payload is actually appended.
///
/// This emulates an oversized-entry ("zip bomb" style header) sample without having to allocate
/// the declared number of bytes. The tar stream is terminated right after the small payload, so
/// the budget pre-scan must reject the entry purely from its header.
fn create_archive_with_oversized_header(
    temp_dir: &assert_fs::TempDir,
    archive_name: &str,
    entry_name: &str,
    declared_size: u64,
    actual_payload: &[u8],
) -> Result<()> {
    let archive_path = temp_dir.path().join(archive_name);
    let tar_gz = File::create(archive_path)?;
    let encoder = GzEncoder::new(tar_gz, Compression::default());
    let mut builder = TarBuilder::new(encoder);

    let mut header = TarHeader::new_gnu();
    header.set_path(entry_name)?;
    header.set_size(declared_size);
    header.set_mode(0o644);
    header.set_entry_type(tar::EntryType::Regular);
    header.set_cksum();
    builder.append(&header, actual_payload)?;

    builder.finish()?;
    Ok(())
}

/// A raw tar entry whose header size and name are written verbatim, which makes it possible to
/// craft traversal paths and header/payload size mismatches that the safe builder API rejects.
struct RawTarEntry<'a> {
    name: &'a str,
    payload: &'a [u8],
}

impl<'a> RawTarEntry<'a> {
    fn new(name: &'a str, payload: &'a [u8]) -> Self {
        Self { name, payload }
    }
}

/// Builds a tar.gz archive from raw 512-byte tar headers, allowing entries with traversal
/// sequences (for example `../name`) that the safe `tar::Builder` API refuses to create.
fn create_raw_tar_gz(
    temp_dir: &assert_fs::TempDir,
    archive_name: &str,
    entries: Vec<RawTarEntry>,
) -> Result<()> {
    let archive_path = temp_dir.path().join(archive_name);
    let tar_gz = File::create(archive_path)?;
    let mut encoder = GzEncoder::new(tar_gz, Compression::default());

    for entry in entries {
        let raw_name = entry.name;
        let payload = entry.payload;
        let mut header_block = [0_u8; 512];
        let name_bytes = raw_name.as_bytes();
        assert!(
            name_bytes.len() < 100,
            "raw tar name must fit the classic name field"
        );
        header_block[..name_bytes.len()].copy_from_slice(name_bytes);

        fn write_octal(field: &mut [u8], value: u64) {
            let field_len = field.len();
            let rendered = format!("{value:0width$o}", width = field_len - 1);
            field[..field_len - 1].copy_from_slice(rendered.as_bytes());
        }

        write_octal(&mut header_block[100..108], 0o644);
        write_octal(&mut header_block[108..116], 0);
        write_octal(&mut header_block[116..124], 0);
        write_octal(&mut header_block[124..136], payload.len() as u64);
        write_octal(&mut header_block[136..148], 0);
        header_block[156] = b'0'; // regular file type flag

        // The checksum field is treated as eight spaces while computing the checksum.
        let mut checksum: u32 = header_block.iter().map(|byte| u32::from(*byte)).sum();
        checksum += u32::from(b' ') * 8;
        let checksum_rendered = format!("{checksum:06o}\0 ");
        header_block[148..156].copy_from_slice(checksum_rendered.as_bytes());

        encoder.write_all(&header_block)?;
        encoder.write_all(payload)?;

        let padding = (512 - payload.len() % 512) % 512;
        if padding > 0 {
            encoder.write_all(&vec![0_u8; padding])?;
        }
    }

    encoder.write_all(&[0_u8; 1024])?;
    encoder.finish()?;
    Ok(())
}

/// Enables code coverage for `tracing::debug` calls.
fn init_test_logger() {
    let _ = fmt::Subscriber::builder()
        .with_max_level(Level::DEBUG)
        .with_test_writer()
        .try_init();
}

/// Given: A tar.gz archive with files and a destination directory
/// When: safe_extract_archive is called with default options
/// Then: The archive is extracted successfully with correct file contents
#[test]
fn test_safe_extract_archive_success() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    create_test_archive(
        &temp_dir,
        "test.tar.gz",
        vec![
            ArchiveEntry::file("file1.txt", "content of file 1"),
            ArchiveEntry::file("file2.txt", "content of file 2"),
            ArchiveEntry::directory("subdir/"),
            ArchiveEntry::file("subdir/file3.txt", "content of file 3"),
            ArchiveEntry::file("level1/level2/nested_file.txt", "nested content"),
            ArchiveEntry::directory("deep/nested/directory/"),
            ArchiveEntry::file("another/deep/path/deep_file.txt", "deep content"),
        ],
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "test.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default().build().unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert!(result.is_ok());

    let file1_path = dest_dir.path().join("file1.txt");
    let file2_path = dest_dir.path().join("file2.txt");
    let file3_path = dest_dir.path().join("subdir/file3.txt");

    assert!(file1_path.exists());
    assert!(file2_path.exists());
    assert!(file3_path.exists());

    assert_eq!(read_to_string(file1_path)?, "content of file 1");
    assert_eq!(read_to_string(file2_path)?, "content of file 2");
    assert_eq!(read_to_string(file3_path)?, "content of file 3");

    let nested_file_path = dest_dir.path().join("level1/level2/nested_file.txt");
    let deep_dir_path = dest_dir.path().join("deep/nested/directory");
    let deep_file_path = dest_dir.path().join("another/deep/path/deep_file.txt");

    assert!(nested_file_path.exists());
    assert!(deep_dir_path.exists() && deep_dir_path.is_dir());
    assert!(deep_file_path.exists());

    assert_eq!(read_to_string(nested_file_path)?, "nested content");
    assert_eq!(read_to_string(deep_file_path)?, "deep content");

    Ok(())
}

/// Given: A tar.gz archive and unauthorized user for reading
/// When: safe_extract_archive is called
/// Then: Access is denied for read permission
#[test]
fn test_unauthorized_safe_extract_archive_read() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (_dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    create_test_archive(
        &temp_dir,
        "test.tar.gz",
        vec![ArchiveEntry::file("file1.txt", "content")],
    )?;

    let principal = get_test_rex_principal();
    let test_policy = format!(
        r#"forbid(
            principal == User::"{principal}",
            action == {},
            resource
        );"#,
        FilesystemAction::Read
    );
    let test_cedar_auth = TestCedarAuthBuilder::default()
        .policy(test_policy)
        .build()
        .unwrap()
        .create();

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "test.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default().build().unwrap();

    let result = archive_handle.safe_extract_archive(&test_cedar_auth, dest_handle, options);

    let expected_error = format!(
        "Permission denied: {principal} unauthorized to perform {}",
        FilesystemAction::Read
    );
    assert_error_contains(result, &expected_error);

    Ok(())
}

/// Given: An archive file opened without read option
/// When: safe_extract_archive is called
/// Then: An error is returned indicating missing read option
#[test]
fn test_safe_extract_archive_no_read_option() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (_dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    create_test_archive(
        &temp_dir,
        "test.tar.gz",
        vec![ArchiveEntry::file("file1.txt", "content")],
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "test.tar.gz",
        OpenFileOptionsBuilder::default()
            .write(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default().build().unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert_error_contains(result, READ_FILE_FLAG_ERR);

    Ok(())
}

/// Given: A tar.gz archive and unauthorized user for file operations during extraction
/// When: safe_extract_archive is called
/// Then: Extraction behavior varies based on the denied file operation
#[rstest]
#[case::create_denied(FilesystemAction::Create, false)]
#[case::write_denied(FilesystemAction::Write, false)]
#[case::chmod_denied(FilesystemAction::Chmod, true)]
#[case::chown_denied(FilesystemAction::Chown, true)]
fn test_unauthorized_safe_extract_archive_file_operations(
    #[case] denied_action: FilesystemAction,
    #[case] file_should_exist: bool,
) -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (_dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    create_test_archive(
        &temp_dir,
        "test.tar.gz",
        vec![ArchiveEntry::file("file1.txt", "content")],
    )?;

    let principal = get_test_rex_principal();
    let dest_file_path = format!("{}/file1.txt", dest_dir_path);

    let test_policy = format!(
        r#"permit(
            principal == User::"{principal}",
            action,
            resource
        );
        forbid(
            principal == User::"{principal}",
            action == {},
            resource == file_system::File::"{dest_file_path}"
        );"#,
        denied_action
    );

    let test_cedar_auth = TestCedarAuthBuilder::default()
        .policy(test_policy)
        .build()
        .unwrap()
        .create();

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "test.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options =
        if denied_action == FilesystemAction::Chmod || denied_action == FilesystemAction::Chown {
            ExtractArchiveOptionsBuilder::default()
                .preserve_permissions(true)
                .preserve_ownership(true)
                .build()
                .unwrap()
        } else {
            ExtractArchiveOptionsBuilder::default().build().unwrap()
        };

    let result = archive_handle.safe_extract_archive(&test_cedar_auth, dest_handle, options);

    assert!(result.is_ok());

    let file_path = Path::new(&dest_dir_path).join("file1.txt");
    if file_should_exist {
        assert!(file_path.exists());
        assert_eq!(read_to_string(&file_path)?, "content");
    } else {
        assert!(!file_path.exists());
    }

    Ok(())
}

/// Given: A tar.gz archive with files that already exist in destination
/// When: safe_extract_archive is called
/// Then: Files are overwritten
#[test]
fn test_safe_extract_archive_overwrite_files() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    let existing_file = dest_dir.child("file1.txt");
    existing_file.write_str("existing content")?;

    let new_content = "new content";
    create_test_archive(
        &temp_dir,
        "test.tar.gz",
        vec![ArchiveEntry::file("file1.txt", new_content)],
    )?;
    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "test.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default().build().unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert!(result.is_ok());

    let file_content = read_to_string(existing_file.path())?;
    assert_eq!(file_content, new_content);

    Ok(())
}

/// Given: A tar.gz archive with special file types (symlinks, devices, etc.)
/// When: safe_extract_archive is called
/// Then: Special file types are skipped and regular files are extracted
#[test]
fn test_safe_extract_archive_skip_special_files() -> Result<()> {
    init_test_logger();

    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    let content = "regular";

    create_test_archive(
        &temp_dir,
        "special.tar.gz",
        vec![
            ArchiveEntry::file("regular.txt", content),
            ArchiveEntry::special_file("symlink", tar::EntryType::Symlink),
            ArchiveEntry::special_file("chardev", tar::EntryType::Char),
        ],
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "special.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default().build().unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert!(result.is_ok());

    let regular_file = dest_dir.path().join("regular.txt");
    assert!(regular_file.exists());
    assert_eq!(read_to_string(regular_file)?, "regular");

    assert!(!dest_dir.path().join("symlink").exists());
    assert!(!dest_dir.path().join("chardev").exists());

    Ok(())
}

/// Given: A tar.gz archive with files and directories having specific permissions
/// When: safe_extract_archive is called with preserve_permissions option
/// Then: Permissions are preserved or set to default based on the option
#[rstest::rstest]
#[case::preserve_true(true)]
#[case::preserve_false(false)]
fn test_safe_extract_archive_preserve_permissions(
    #[case] preserve_permissions: bool,
) -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    let file_mode = 0o700;
    let dir_mode = 0o700;

    create_test_archive(
        &temp_dir,
        "test.tar.gz",
        vec![
            ArchiveEntry::file("executable.sh", "content").with_mode(file_mode),
            ArchiveEntry::directory("test_directory/").with_mode(dir_mode),
        ],
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "test.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default()
        .preserve_permissions(preserve_permissions)
        .build()
        .unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);
    assert!(result.is_ok());

    let extracted_file = dest_dir.path().join("executable.sh");
    let extracted_dir = dest_dir.path().join("test_directory");

    assert!(extracted_file.exists());
    assert!(extracted_dir.exists() && extracted_dir.is_dir());

    let file_metadata = metadata(&extracted_file)?;
    let dir_metadata = metadata(&extracted_dir)?;

    let actual_file_mode = file_metadata.mode() & PERMISSION_EXTRACT_BITMASK;
    let actual_dir_mode = dir_metadata.mode() & PERMISSION_EXTRACT_BITMASK;

    if preserve_permissions {
        assert_eq!(actual_file_mode, file_mode);
        assert_eq!(actual_dir_mode, dir_mode);
    } else {
        assert_ne!(actual_file_mode, file_mode);
        assert_ne!(actual_dir_mode, dir_mode);
    }

    Ok(())
}

/// Given: A tar.gz archive with files and directories having specific timestamps
/// When: safe_extract_archive is called with preserve_timestamps option
/// Then: Timestamps are preserved or set to current time based on the option
#[rstest::rstest]
#[case::preserve_true(true)]
#[case::preserve_false(false)]
fn test_safe_extract_archive_preserve_timestamps(#[case] preserve_timestamps: bool) -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    let custom_mtime = 1609459200;

    create_test_archive(
        &temp_dir,
        "test.tar.gz",
        vec![
            ArchiveEntry::file("timestamped_file.txt", "content").with_mtime(custom_mtime),
            ArchiveEntry::directory("timestamped_directory/").with_mtime(custom_mtime),
        ],
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "test.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default()
        .preserve_timestamps(preserve_timestamps)
        .build()
        .unwrap();

    let before_extraction = SystemTime::now() - Duration::from_millis(100);
    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);
    let after_extraction = SystemTime::now() + Duration::from_millis(100);

    assert!(result.is_ok());

    let extracted_file = dest_dir.path().join("timestamped_file.txt");
    let extracted_dir = dest_dir.path().join("timestamped_directory");

    assert!(extracted_file.exists());
    assert!(extracted_dir.exists() && extracted_dir.is_dir());

    let file_metadata = metadata(&extracted_file)?;
    let dir_metadata = metadata(&extracted_dir)?;

    let file_mtime = file_metadata.modified()?;
    let dir_mtime = dir_metadata.modified()?;

    if preserve_timestamps {
        let expected_time = UNIX_EPOCH + Duration::from_secs(custom_mtime);

        assert_eq!(file_mtime, expected_time);
        assert_eq!(dir_mtime, expected_time);
    } else {
        assert!(file_mtime >= before_extraction);
        assert!(file_mtime <= after_extraction);
        assert!(dir_mtime >= before_extraction);
        assert!(dir_mtime <= after_extraction);
    }

    Ok(())
}

/// Given: A tar.gz archive and unauthorized user for directory operations during extraction
/// When: safe_extract_archive is called
/// Then: Extraction behavior varies based on the denied directory operation
#[rstest]
#[case::create_denied(FilesystemAction::Create, false)]
#[case::chmod_denied(FilesystemAction::Chmod, true)]
#[case::chown_denied(FilesystemAction::Chown, true)]
fn test_unauthorized_safe_extract_archive_directory_operations(
    #[case] denied_action: FilesystemAction,
    #[case] dir_should_exist: bool,
) -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (_dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    create_test_archive(
        &temp_dir,
        "test.tar.gz",
        vec![
            ArchiveEntry::directory("test_directory/"),
            ArchiveEntry::file("test_directory/file.txt", "content"),
        ],
    )?;

    let principal = get_test_rex_principal();
    let dest_directory_path = format!("{}/test_directory", dest_dir_path);

    let test_policy = format!(
        r#"permit(
            principal == User::"{principal}",
            action,
            resource
        );
        forbid(
            principal == User::"{principal}",
            action == {},
            resource == file_system::Dir::"{dest_directory_path}"
        );"#,
        denied_action
    );

    let test_cedar_auth = TestCedarAuthBuilder::default()
        .policy(test_policy)
        .build()
        .unwrap()
        .create();

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "test.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options =
        if denied_action == FilesystemAction::Chmod || denied_action == FilesystemAction::Chown {
            ExtractArchiveOptionsBuilder::default()
                .preserve_permissions(true)
                .preserve_ownership(true)
                .build()
                .unwrap()
        } else {
            ExtractArchiveOptionsBuilder::default().build().unwrap()
        };

    let result = archive_handle.safe_extract_archive(&test_cedar_auth, dest_handle, options);

    assert!(result.is_ok());

    let directory_path = std::path::Path::new(&dest_dir_path).join("test_directory");
    let file_path = directory_path.join("file.txt");

    if dir_should_exist {
        assert!(directory_path.exists() && directory_path.is_dir());
        assert!(file_path.exists());
        assert_eq!(read_to_string(&file_path)?, "content");
    } else {
        assert!(!directory_path.exists());
        assert!(!file_path.exists());
    }

    Ok(())
}

/// Given: A tar.gz archive with nested directories and authorization denied for intermediate directory
/// When: safe_extract_archive is called
/// Then: Warning is logged for directory creation failure but extraction continues
#[test]
fn test_safe_extract_archive_nested_directory_creation_failure() -> Result<()> {
    init_test_logger();

    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    create_test_archive(
        &temp_dir,
        "test.tar.gz",
        vec![ArchiveEntry::directory("parent/child/grandchild/")],
    )?;

    let principal = get_test_rex_principal();
    let intermediate_dir_path = format!("{}/parent/child", dest_dir_path);
    let test_policy = format!(
        r#"permit(
            principal == User::"{principal}",
            action,
            resource
        );
        forbid(
            principal == User::"{principal}",
            action == {},
            resource == file_system::Dir::"{intermediate_dir_path}"
        );"#,
        FilesystemAction::Create
    );
    let test_cedar_auth = TestCedarAuthBuilder::default()
        .policy(test_policy)
        .build()
        .unwrap()
        .create();

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "test.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default().build().unwrap();

    let result = archive_handle.safe_extract_archive(&test_cedar_auth, dest_handle, options);

    assert!(result.is_ok());

    let nested_dir = dest_dir.path().join("parent/child/grandchild");
    assert!(!nested_dir.exists());

    let parent_dir = dest_dir.path().join("parent");
    assert!(!parent_dir.exists());

    Ok(())
}

/// Given: A tar.gz archive with directories having timestamps and permissions that fail to set
/// When: safe_extract_archive is called with preserve_timestamps=true and preserve_permissions=true
/// Then: Warnings are logged but extraction continues successfully
#[test]
fn test_safe_extract_archive_directory_timestamp_and_permission_failure_warning() -> Result<()> {
    init_test_logger();

    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    let custom_mtime = 1609459200;
    let custom_mode = 0o700;

    let problem_dir = dest_dir.child("test_dir");
    problem_dir.create_dir_all()?;

    let original_mode = metadata(problem_dir.path())?.mode() & PERMISSION_EXTRACT_BITMASK;

    set_permissions(problem_dir.path(), Permissions::from_mode(0o000))?;

    create_test_archive(
        &temp_dir,
        "test.tar.gz",
        vec![
            ArchiveEntry::directory("test_dir/")
                .with_mtime(custom_mtime)
                .with_mode(custom_mode),
        ],
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "test.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default()
        .preserve_timestamps(true)
        .preserve_permissions(true)
        .build()
        .unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    set_permissions(problem_dir.path(), Permissions::from_mode(original_mode))?;

    assert!(result.is_ok());
    assert!(problem_dir.exists());
    assert!(problem_dir.is_dir());

    let final_mode = metadata(problem_dir.path())?.mode() & PERMISSION_EXTRACT_BITMASK;
    assert_ne!(final_mode, custom_mode);

    Ok(())
}

/// Given: An empty tar.gz archive
/// When: safe_extract_archive is called
/// Then: Extraction succeeds with no files created
#[test]
fn test_safe_extract_archive_empty() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    create_test_archive(&temp_dir, "empty.tar.gz", vec![])?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "empty.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default().build().unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert!(result.is_ok());

    let dest_entries: Vec<_> =
        read_dir(dest_dir.path())?.collect::<std::result::Result<Vec<_>, _>>()?;
    assert_eq!(dest_entries.len(), 0);

    Ok(())
}

/// Given: A tar.gz archive with nested directories having specific permissions
/// When: safe_extract_archive is called with preserve_permissions=true
/// Then: Both intermediate and final directory permissions are preserved
#[test]
fn test_safe_extract_archive_preserve_intermediate_directory_permissions() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    let parent_mode = 0o755;
    let child_mode = 0o700;
    let grandchild_mode = 0o750;

    create_test_archive(
        &temp_dir,
        "nested.tar.gz",
        vec![
            ArchiveEntry::directory("parent/").with_mode(parent_mode),
            ArchiveEntry::directory("parent/child/").with_mode(child_mode),
            ArchiveEntry::directory("parent/child/grandchild/").with_mode(grandchild_mode),
            ArchiveEntry::file("parent/child/grandchild/file.txt", "content"),
        ],
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "nested.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default()
        .preserve_permissions(true)
        .build()
        .unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert!(result.is_ok());

    let parent_dir = dest_dir.path().join("parent");
    let child_dir = dest_dir.path().join("parent/child");
    let grandchild_dir = dest_dir.path().join("parent/child/grandchild");
    let nested_file = dest_dir.path().join("parent/child/grandchild/file.txt");

    assert!(parent_dir.exists() && parent_dir.is_dir());
    assert!(child_dir.exists() && child_dir.is_dir());
    assert!(grandchild_dir.exists() && grandchild_dir.is_dir());
    assert!(nested_file.exists() && nested_file.is_file());

    let parent_metadata = metadata(&parent_dir)?;
    let child_metadata = metadata(&child_dir)?;
    let grandchild_metadata = metadata(&grandchild_dir)?;

    let parent_actual_mode = parent_metadata.mode() & PERMISSION_EXTRACT_BITMASK;
    let child_actual_mode = child_metadata.mode() & PERMISSION_EXTRACT_BITMASK;
    let grandchild_actual_mode = grandchild_metadata.mode() & PERMISSION_EXTRACT_BITMASK;

    assert_eq!(parent_actual_mode, parent_mode);
    assert_eq!(child_actual_mode, child_mode);
    assert_eq!(grandchild_actual_mode, grandchild_mode);

    Ok(())
}

/// Given: A file that is not actually gzip compressed
/// When: safe_extract_archive is called
/// Then: Extraction fails gracefully with an "invalid gzip" error
#[test]
fn test_safe_extract_archive_invalid_tar_gz() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (_dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    let fake_gz_file = temp_dir.child("fake.tar");
    fake_gz_file.write_str("This is just plain text, not gzip compressed data!")?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "fake.tar",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default().build().unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert!(result.is_err());
    assert_error_contains(result, "invalid gzip");

    Ok(())
}

/// Given: A tar.gz archive whose regular entries exceed the configured total byte budget
/// When: safe_extract_archive is called with max_extracted_bytes
/// Then: Extraction fails with a budget error and no entry is written to the destination
#[test]
fn test_safe_extract_archive_total_bytes_budget_exceeded() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    create_test_archive(
        &temp_dir,
        "budget.tar.gz",
        vec![
            ArchiveEntry::file("file1.txt", "0123456789"),
            ArchiveEntry::file("file2.txt", "0123456789"),
        ],
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "budget.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default()
        .max_extracted_bytes(15_u64)
        .build()
        .unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert!(result.is_err());
    assert_error_contains(result, "Archive extraction budget exceeded");

    assert!(!Path::new(&dest_dir_path).join("file1.txt").exists());
    assert!(!Path::new(&dest_dir_path).join("file2.txt").exists());

    let dest_entries: Vec<_> =
        read_dir(dest_dir.path())?.collect::<std::result::Result<Vec<_>, _>>()?;
    assert!(
        dest_entries.is_empty(),
        "budget failure must not leave partial extraction"
    );

    Ok(())
}

/// Given: A tar.gz archive with a single regular entry larger than the per-entry budget
/// When: safe_extract_archive is called with max_entry_size_bytes
/// Then: Extraction fails with a budget error and the entry is not extracted
#[test]
fn test_safe_extract_archive_entry_size_budget_exceeded() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (_dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    create_test_archive(
        &temp_dir,
        "entry_budget.tar.gz",
        vec![ArchiveEntry::file(
            "large.txt",
            "this content is thirty bytes long!",
        )],
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "entry_budget.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default()
        .max_entry_size_bytes(10_u64)
        .build()
        .unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert!(result.is_err());
    assert_error_contains(result, "single entry size limit exceeded");
    assert!(!Path::new(&dest_dir_path).join("large.txt").exists());

    Ok(())
}

/// Given: A tar.gz archive containing more entries than the configured entry count budget
/// When: safe_extract_archive is called with max_entry_count
/// Then: Extraction fails with a budget error before anything is written and directories count too
#[test]
fn test_safe_extract_archive_entry_count_budget_exceeded() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (_dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    create_test_archive(
        &temp_dir,
        "count.tar.gz",
        vec![
            ArchiveEntry::directory("subdir/"),
            ArchiveEntry::file("subdir/file1.txt", "one"),
            ArchiveEntry::file("subdir/file2.txt", "two"),
        ],
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "count.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default()
        .max_entry_count(2_u64)
        .build()
        .unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert!(result.is_err());
    assert_error_contains(result, "entry count limit exceeded");
    assert!(!Path::new(&dest_dir_path).join("subdir").exists());

    Ok(())
}

/// Given: An archive entry whose header declares an enormous size but carries little payload
/// When: safe_extract_archive is called with a smaller per-entry budget
/// Then: The header-only pre-scan rejects it without creating any destination path
#[test]
fn test_safe_extract_archive_oversized_header_sample() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    create_archive_with_oversized_header(
        &temp_dir,
        "oversized.tar.gz",
        "bomb.bin",
        1024 * 1024 * 1024,
        b"small actual payload",
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "oversized.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default()
        .max_entry_size_bytes(1024_u64)
        .build()
        .unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert!(result.is_err());
    assert_error_contains(result, "single entry size limit exceeded");
    assert!(!Path::new(&dest_dir_path).join("bomb.bin").exists());

    let dest_entries: Vec<_> =
        read_dir(dest_dir.path())?.collect::<std::result::Result<Vec<_>, _>>()?;
    assert!(dest_entries.is_empty());

    Ok(())
}

/// Given: A tar.gz archive whose entries stay within every configured budget
/// When: safe_extract_archive is called with budgets set at or above the archive sizes
/// Then: Extraction succeeds and file contents are correct
#[test]
fn test_safe_extract_archive_within_budgets() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (_dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    create_test_archive(
        &temp_dir,
        "within.tar.gz",
        vec![
            ArchiveEntry::file("file1.txt", "content-one"),
            ArchiveEntry::file("file2.txt", "content-two"),
        ],
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "within.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default()
        .max_extracted_bytes(100_u64)
        .max_entry_size_bytes(50_u64)
        .max_entry_count(2_u64)
        .build()
        .unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert!(result.is_ok());
    assert_eq!(
        read_to_string(Path::new(&dest_dir_path).join("file1.txt"))?,
        "content-one"
    );
    assert_eq!(
        read_to_string(Path::new(&dest_dir_path).join("file2.txt"))?,
        "content-two"
    );

    Ok(())
}

/// Given: A tar.gz archive containing a path traversal (prefix escape) entry
/// When: safe_extract_archive is called with a budget configured
/// Then: The traversal entry never escapes the destination directory and normal entries extract
#[test]
fn test_safe_extract_archive_prefix_traversal_sample() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    create_raw_tar_gz(
        &temp_dir,
        "prefix.tar.gz",
        vec![
            RawTarEntry::new("../escaped.txt", b"must stay inside"),
            RawTarEntry::new("safe.txt", b"inside content"),
        ],
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "prefix.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default()
        .max_extracted_bytes(1024_u64)
        .max_entry_size_bytes(1024_u64)
        .max_entry_count(10_u64)
        .build()
        .unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert!(result.is_ok());
    assert!(!Path::new(&dest_dir_path).join("../escaped.txt").exists());
    assert!(
        !dest_dir
            .path()
            .parent()
            .unwrap()
            .join("escaped.txt")
            .exists()
    );
    assert_eq!(
        read_to_string(Path::new(&dest_dir_path).join("safe.txt"))?,
        "inside content"
    );

    Ok(())
}

/// Given: A destination directory holding pre-existing files and a budget that will be exceeded
/// When: safe_extract_archive fails the pre-scan
/// Then: Pre-existing files are untouched and no partial extraction artifacts remain
#[test]
fn test_safe_extract_archive_budget_failure_preserves_preexisting_files() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    let existing = dest_dir.child("existing.txt");
    existing.write_str("keep me")?;

    create_test_archive(
        &temp_dir,
        "mix.tar.gz",
        vec![ArchiveEntry::file("new.txt", "x".repeat(100).as_str())],
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "mix.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default()
        .max_extracted_bytes(10_u64)
        .build()
        .unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert!(result.is_err());
    assert_eq!(read_to_string(existing.path())?, "keep me");
    assert!(!Path::new(&dest_dir_path).join("new.txt").exists());

    Ok(())
}

/// Given: An entry whose streaming payload exceeds the configured per-entry byte limit
/// When: safe_extract_archive streams the entry with a smaller max_entry_size_bytes
/// Then: The streaming budget guard aborts the copy and rollback leaves no extracted file
#[test]
fn test_safe_extract_archive_streaming_guard_enforces_entry_limit() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    create_raw_tar_gz(
        &temp_dir,
        "malformed.tar.gz",
        vec![RawTarEntry::new("data.bin", b"0123456789abcdef")],
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "malformed.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default()
        .max_extracted_bytes(1024_u64)
        .max_entry_size_bytes(8_u64)
        .max_entry_count(10_u64)
        .build()
        .unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert!(result.is_err());
    assert_error_contains(result, "Archive extraction budget exceeded");
    assert!(!Path::new(&dest_dir_path).join("data.bin").exists());

    let dest_entries: Vec<_> =
        read_dir(dest_dir.path())?.collect::<std::result::Result<Vec<_>, _>>()?;
    assert!(dest_entries.is_empty());

    Ok(())
}

/// Given: An archive where an earlier entry extracts successfully and a later entry exceeds the budget
/// When: safe_extract_archive fails midway
/// Then: Rollback removes every already-created path, including nested directories and files
#[test]
fn test_safe_extract_archive_rolls_back_partial_extraction() -> Result<()> {
    let (temp_dir, temp_dir_path) = create_temp_dir_and_path()?;
    let (dest_dir, dest_dir_path) = create_temp_dir_and_path()?;

    create_test_archive(
        &temp_dir,
        "partial.tar.gz",
        vec![
            ArchiveEntry::directory("already/created/nested/"),
            ArchiveEntry::file("already/created/nested/first.txt", "first file content"),
            ArchiveEntry::file("second.txt", "x".repeat(200).as_str()),
        ],
    )?;

    let dir_handle = open_test_dir_handle(&temp_dir_path);
    let dest_handle = open_test_dir_handle(&dest_dir_path);

    let archive_handle = dir_handle.safe_open_file(
        &DEFAULT_TEST_CEDAR_AUTH,
        "partial.tar.gz",
        OpenFileOptionsBuilder::default()
            .read(true)
            .build()
            .unwrap(),
    )?;

    let options = ExtractArchiveOptionsBuilder::default()
        .max_entry_size_bytes(100_u64)
        .build()
        .unwrap();

    let result =
        archive_handle.safe_extract_archive(&DEFAULT_TEST_CEDAR_AUTH, dest_handle, options);

    assert!(result.is_err());
    assert_error_contains(result, "single entry size limit exceeded");

    assert!(!Path::new(&dest_dir_path).join("already").exists());
    assert!(!Path::new(&dest_dir_path).join("second.txt").exists());

    let dest_entries: Vec<_> =
        read_dir(dest_dir.path())?.collect::<std::result::Result<Vec<_>, _>>()?;
    assert!(
        dest_entries.is_empty(),
        "rollback must remove all partial extraction paths"
    );

    Ok(())
}
