pub mod terminal;

use std::io::Read;
use std::path::{Path, PathBuf};
use std::{fs, io};

/// A span in the source code.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SourceCode {
    /// All the source files pulled in to the project.
    files: Vec<SourceFile>,
    length: usize,
}

impl SourceCode {
    pub fn new(files: impl Into<Vec<SourceFile>>) -> Self {
        let files = files.into();
        let length = files.iter().fold(0, |acc, f| acc + f.len());
        Self { files, length }
    }

    pub fn add_file(&mut self, path: impl Into<PathBuf>) -> io::Result<&SourceFile> {
        let file = SourceFile::load_file(path, self.length)?;
        self.length += file.len();
        self.files.push(file);
        Ok(&self.files[self.files.len() - 1])
    }

    pub fn add_reader<R: Read>(
        &mut self,
        file_name: impl Into<PathBuf>,
        file: R,
    ) -> io::Result<&SourceFile> {
        let file = SourceFile::load_reader(file_name, file, self.length)?;
        self.length += file.len();
        self.files.push(file);
        Ok(&self.files[self.files.len() - 1])
    }

    pub fn len(&self) -> usize {
        self.length
    }

    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    pub fn files(&self) -> &[SourceFile] {
        &self.files
    }
}

/// A span in the source code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceFile {
    file_path: PathBuf,
    content: String,
    /// The byte offset into `SourceCode`. All SourceFiles are are considered to exist
    /// one after the other.
    offset: usize,
}

impl SourceFile {
    pub fn from_string(s: impl Into<String>, offset: usize) -> Self {
        Self {
            file_path: "<generated>".into(),
            content: s.into(),
            offset,
        }
    }

    pub fn load_file(file_path: impl Into<PathBuf>, offset: usize) -> io::Result<Self> {
        let file_path = file_path.into();
        let content = fs::read_to_string(&file_path)?;

        Ok(Self {
            file_path,
            content,
            offset,
        })
    }

    pub fn load_reader<R: Read>(
        file_name: impl Into<PathBuf>,
        mut reader: R,
        offset: usize,
    ) -> io::Result<Self> {
        let mut content = String::new();
        reader.read_to_string(&mut content)?;

        Ok(Self {
            file_path: file_name.into(),
            content,
            offset,
        })
    }

    pub fn len(&self) -> usize {
        self.content.len()
    }

    pub fn is_empty(&self) -> bool {
        self.content.is_empty()
    }

    pub fn offset(&self) -> usize {
        self.offset
    }

    pub fn file_path(&self) -> &Path {
        &self.file_path
    }

    pub fn content(&self) -> &str {
        &self.content
    }
}

/// A span in the source code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub lo: u32,
    pub hi: u32,
}

impl Span {
    pub fn new(lo: u32, hi: u32) -> Self {
        Self { lo, hi }
    }

    /// Create a new Span (self.lo, other.end).
    pub fn extend(self, end: Self) -> Self {
        Self {
            lo: self.lo,
            hi: end.hi,
        }
    }
}
