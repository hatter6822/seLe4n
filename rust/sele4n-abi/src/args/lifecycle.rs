//! Lifecycle syscall argument structures.
//!
//! Lean: `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` lines 109–115.

use sele4n_types::{ObjId, KernelError, KernelResult};

/// Arguments for `lifecycleRetype` (syscall 8).
/// Register mapping: x2=targetObj, x3=newType tag, x4=size hint.
///
/// Lean: `LifecycleRetypeArgs` (SyscallArgDecode.lean:111)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LifecycleRetypeArgs {
    pub target_obj: ObjId,
    pub new_type: u64,
    pub size: u64,
}

impl LifecycleRetypeArgs {
    pub const fn encode(&self) -> [u64; 3] {
        [self.target_obj.raw(), self.new_type, self.size]
    }

    pub fn decode(regs: &[u64]) -> KernelResult<Self> {
        if regs.len() < 3 { return Err(KernelError::InvalidMessageInfo); }
        Ok(Self {
            target_obj: ObjId::from(regs[0]),
            new_type: regs[1],
            size: regs[2],
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        let args = LifecycleRetypeArgs { target_obj: ObjId::from(42u64), new_type: 2, size: 4096 };
        assert_eq!(LifecycleRetypeArgs::decode(&args.encode()).unwrap(), args);
    }

    #[test]
    fn insufficient_regs() {
        assert_eq!(LifecycleRetypeArgs::decode(&[1, 2]), Err(KernelError::InvalidMessageInfo));
    }
}
