use std::hash::Hasher;
use std::u32;

use md5::Context;

pub struct Md5Hasher {
    context: Context,
}

impl Md5Hasher {
    pub fn new() -> Self {
        Md5Hasher { context: Context::new() }
    }
}

impl Hasher for Md5Hasher {
    fn finish(&self) -> u64 {
        let r = self.context.compute();
        let p1 = ((r[0] as u64) << 0) + ((r[1] as u64) << 8) +
            ((r[2] as u64) << 16) + ((r[3] as u64) << 24) +
            ((r[4] as u64) << 32) + ((r[5] as u64) << 40) +
            ((r[6] as u64) << 48) + ((r[7] as u64) << 56);
        let p2 = ((r[8] as u64) << 0) + ((r[9] as u64) << 8) +
            ((r[10] as u64) << 16) + ((r[11] as u64) << 24) +
            ((r[12] as u64) << 32) + ((r[13] as u64) << 40) +
            ((r[14] as u64) << 48) + ((r[15] as u64) << 56);
        // need to make a u64 from a u128
        p1 % (u32::MAX as u64) + p2 % (u32::MAX as u64)
    }

    fn write(&mut self, bytes: &[u8]) {
        self.context.consume(bytes);
    }
}
