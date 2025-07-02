use std::{
    io::{self, Write},
    sync::RwLock,
};

#[allow(dead_code)]
pub struct Utililites {
    write_buffer: RwLock<io::Stdout>,
}

#[allow(dead_code)]
impl Utililites {
    pub fn new() -> Self {
        Utililites {
            write_buffer: RwLock::new(io::stdout()),
        }
    }

    pub fn write_to_cli(&mut self, data: &str) {
        let mut buffer = self.write_buffer.write().unwrap();
        let _ = write!(&mut buffer, "{}", data);
        drop(buffer);
        let _ = std::io::stdout().flush();
    }

    pub fn ensure_equal<T: std::fmt::Debug + PartialEq>(&self, a: T, b: T) -> Result<(), ()> {
        if a != b { Err(()) } else { Ok(()) }
    }
}
