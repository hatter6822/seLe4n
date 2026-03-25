//! RegisterFile — safe, bounds-checked wrapper for syscall register arrays.
//!
//! U3-G / U-L09: Replaces raw `[u64; 7]` array indexing with a type that
//! returns `Option` for out-of-bounds access instead of panicking.
//!
//! The ARM64 syscall ABI uses 7 logical register slots:
//! - Index 0: x0 (CPtr / error code)
//! - Index 1: x1 (MessageInfo / badge)
//! - Index 2–5: x2–x5 (message registers)
//! - Index 6: x7 (syscall number)

/// Number of registers in the syscall ABI.
pub const NUM_REGS: usize = 7;

/// Safe, bounds-checked wrapper around the 7-element ARM64 syscall register array.
///
/// All access methods return `Option` or `Result` instead of panicking on
/// out-of-bounds indices. This prevents undefined behavior in release builds
/// where `debug_assert!` would be stripped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RegisterFile {
    regs: [u64; NUM_REGS],
}

impl RegisterFile {
    /// Create a zeroed register file.
    pub const fn new() -> Self {
        Self { regs: [0; NUM_REGS] }
    }

    /// Create from a raw array.
    pub const fn from_array(regs: [u64; NUM_REGS]) -> Self {
        Self { regs }
    }

    /// Get a register value by index. Returns `None` for indices >= 7.
    #[inline]
    pub fn get(&self, idx: usize) -> Option<u64> {
        self.regs.get(idx).copied()
    }

    /// Set a register value by index. Returns `None` if the index is
    /// out of bounds (>= 7), `Some(())` on success.
    #[inline]
    pub fn set(&mut self, idx: usize, val: u64) -> Option<()> {
        let slot = self.regs.get_mut(idx)?;
        *slot = val;
        Some(())
    }

    /// Convert to the underlying raw array.
    #[inline]
    pub const fn into_array(self) -> [u64; NUM_REGS] {
        self.regs
    }

    /// Borrow the underlying raw array.
    #[inline]
    pub const fn as_array(&self) -> &[u64; NUM_REGS] {
        &self.regs
    }

    /// Mutably borrow the underlying raw array.
    #[inline]
    pub fn as_array_mut(&mut self) -> &mut [u64; NUM_REGS] {
        &mut self.regs
    }
}

impl Default for RegisterFile {
    fn default() -> Self { Self::new() }
}

impl From<[u64; NUM_REGS]> for RegisterFile {
    fn from(regs: [u64; NUM_REGS]) -> Self { Self::from_array(regs) }
}

impl From<RegisterFile> for [u64; NUM_REGS] {
    fn from(rf: RegisterFile) -> Self { rf.into_array() }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_is_zeroed() {
        let rf = RegisterFile::new();
        for i in 0..NUM_REGS {
            assert_eq!(rf.get(i), Some(0));
        }
    }

    #[test]
    fn get_out_of_bounds_returns_none() {
        let rf = RegisterFile::new();
        assert_eq!(rf.get(7), None);
        assert_eq!(rf.get(100), None);
        assert_eq!(rf.get(usize::MAX), None);
    }

    #[test]
    fn set_out_of_bounds_returns_none() {
        let mut rf = RegisterFile::new();
        assert_eq!(rf.set(7, 42), None);
        assert_eq!(rf.set(100, 42), None);
    }

    #[test]
    fn set_get_roundtrip() {
        let mut rf = RegisterFile::new();
        for i in 0..NUM_REGS {
            rf.set(i, (i as u64 + 1) * 100).unwrap();
        }
        for i in 0..NUM_REGS {
            assert_eq!(rf.get(i), Some((i as u64 + 1) * 100));
        }
    }

    #[test]
    fn from_array_roundtrip() {
        let arr = [10, 20, 30, 40, 50, 60, 70];
        let rf = RegisterFile::from_array(arr);
        assert_eq!(rf.into_array(), arr);
    }

    #[test]
    fn as_array_matches() {
        let arr = [1, 2, 3, 4, 5, 6, 7];
        let rf = RegisterFile::from(arr);
        assert_eq!(*rf.as_array(), arr);
    }
}
