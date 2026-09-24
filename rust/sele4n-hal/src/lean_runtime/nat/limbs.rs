//! Magnitude arithmetic on little-endian 64-bit limbs.
//!
//! Every function takes its operands normalized (no leading zero limb; zero is
//! the empty slice), writes into a caller-supplied output of the documented
//! length, and returns the normalized length of what it wrote.  Nothing here
//! allocates except through [`super::Scratch`], and nothing here is `unsafe`.

use core::cmp::Ordering;

/// The length of `a` without its leading zero limbs.
#[must_use]
pub fn normalized_len(a: &[u64]) -> usize {
    a.iter().rposition(|&l| l != 0).map_or(0, |i| i + 1)
}

/// Compares two normalized magnitudes.
#[must_use]
pub fn cmp(a: &[u64], b: &[u64]) -> Ordering {
    a.len()
        .cmp(&b.len())
        .then_with(|| a.iter().rev().cmp(b.iter().rev()))
}

/// `out = a + b`.  `out` holds at least `max(|a|, |b|) + 1` limbs, zeroed.
pub fn add(a: &[u64], b: &[u64], out: &mut [u64]) -> usize {
    let (long, short) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let mut carry = 0u64;
    for i in 0..long.len() {
        let (s1, c1) = long[i].overflowing_add(short.get(i).copied().unwrap_or(0));
        let (s2, c2) = s1.overflowing_add(carry);
        out[i] = s2;
        carry = u64::from(c1) + u64::from(c2);
    }
    out[long.len()] = carry;
    normalized_len(&out[..=long.len()])
}

/// `out = a - b` for `a >= b`.  `out` holds at least `|a|` limbs.
pub fn sub(a: &[u64], b: &[u64], out: &mut [u64]) -> usize {
    let mut borrow = 0u64;
    for i in 0..a.len() {
        let (d1, b1) = a[i].overflowing_sub(b.get(i).copied().unwrap_or(0));
        let (d2, b2) = d1.overflowing_sub(borrow);
        out[i] = d2;
        borrow = u64::from(b1) + u64::from(b2);
    }
    debug_assert_eq!(borrow, 0, "limbs::sub requires a >= b");
    normalized_len(&out[..a.len()])
}

/// `out = a * b`, schoolbook.  `out` holds at least `|a| + |b|` limbs, zeroed.
pub fn mul(a: &[u64], b: &[u64], out: &mut [u64]) -> usize {
    if a.is_empty() || b.is_empty() {
        return 0;
    }
    for (i, &x) in a.iter().enumerate() {
        let mut carry = 0u128;
        for (j, &y) in b.iter().enumerate() {
            let t = u128::from(x) * u128::from(y) + u128::from(out[i + j]) + carry;
            out[i + j] = t as u64;
            carry = t >> 64;
        }
        out[i + b.len()] = carry as u64;
    }
    normalized_len(&out[..a.len() + b.len()])
}

/// Adds one to the magnitude in `a[..len]` in place.  `a` has room for a carry.
pub fn increment(a: &mut [u64], len: usize) -> usize {
    for limb in a.iter_mut() {
        let (s, c) = limb.overflowing_add(1);
        *limb = s;
        if !c {
            break;
        }
    }
    normalized_len(&a[..(len + 1).min(a.len())])
}

/// `out = a op b` limb by limb, treating the shorter operand as zero-extended.
pub fn bitwise(a: &[u64], b: &[u64], out: &mut [u64], op: impl Fn(u64, u64) -> u64) -> usize {
    let n = out.len().min(a.len().max(b.len()));
    for (i, o) in out.iter_mut().enumerate().take(n) {
        *o = op(
            a.get(i).copied().unwrap_or(0),
            b.get(i).copied().unwrap_or(0),
        );
    }
    normalized_len(&out[..n])
}

/// `out = a << s`.  `out` holds at least `|a| + s/64 + 1` limbs, zeroed.
pub fn shl(a: &[u64], s: usize, out: &mut [u64]) -> usize {
    if a.is_empty() {
        return 0;
    }
    let (words, bits) = (s / 64, s % 64);
    for (i, &x) in a.iter().enumerate() {
        out[i + words] |= x << bits;
        if bits != 0 {
            out[i + words + 1] |= x >> (64 - bits);
        }
    }
    normalized_len(&out[..a.len() + words + 1])
}

/// `out = a >> s`.  `out` holds at least `|a|` limbs.
pub fn shr(a: &[u64], s: usize, out: &mut [u64]) -> usize {
    let (words, bits) = (s / 64, s % 64);
    if words >= a.len() {
        return 0;
    }
    let n = a.len() - words;
    for i in 0..n {
        let lo = a[i + words] >> bits;
        let hi = if bits != 0 {
            a.get(i + words + 1).map_or(0, |&h| h << (64 - bits))
        } else {
            0
        };
        out[i] = lo | hi;
    }
    normalized_len(&out[..n])
}

/// The index of the highest set bit; zero for zero (`mpz::log2`).
#[must_use]
pub fn log2(a: &[u64]) -> usize {
    match a.last() {
        None => 0,
        Some(&top) => (a.len() - 1) * 64 + (63 - top.leading_zeros() as usize),
    }
}

/// `(q, r) = divmod(a, b)` for nonzero `b`, truncating.  `q` holds at least
/// `|a| - |b| + 1` limbs and `r` at least `|b|`, both zeroed.  Returns the two
/// normalized lengths.  Knuth's Algorithm D (TAOCP vol. 2, §4.3.1), with the
/// one-limb divisor as its own case.
pub fn divrem(a: &[u64], b: &[u64], q: &mut [u64], r: &mut [u64]) -> (usize, usize) {
    assert!(!b.is_empty(), "limbs::divrem by zero");
    if cmp(a, b) == Ordering::Less {
        r[..a.len()].copy_from_slice(a);
        return (0, a.len());
    }
    if b.len() == 1 {
        let d = u128::from(b[0]);
        let mut rem = 0u128;
        for i in (0..a.len()).rev() {
            let cur = (rem << 64) | u128::from(a[i]);
            q[i] = (cur / d) as u64;
            rem = cur % d;
        }
        r[0] = rem as u64;
        return (normalized_len(&q[..a.len()]), normalized_len(&r[..1]));
    }
    let n = b.len();
    let m = a.len() - n;
    let shift = b[n - 1].leading_zeros() as usize;
    let mut un_s = super::Scratch::new(a.len() + 1);
    // Both shifted operands get a spare top limb for `shl` to write into.
    let mut vn_s = super::Scratch::new(n + 1);
    let un = un_s.slice();
    let vn = vn_s.slice();
    shl(a, shift, un);
    shl(b, shift, vn);
    let vtop = u128::from(vn[n - 1]);
    let vnext = u128::from(vn[n - 2]);
    for j in (0..=m).rev() {
        let num = (u128::from(un[j + n]) << 64) | u128::from(un[j + n - 1]);
        let mut qhat = num / vtop;
        let mut rhat = num % vtop;
        // Normalization is what bounds this loop: with the divisor's top bit
        // set, the estimate is at most two too large (Knuth, Theorem 4.3.1B),
        // so the loop runs at most twice.  Without it the quotient still comes
        // out right, but only after up to 2^shift corrections — division time
        // would depend on the divisor's magnitude, which the assertion refuses.
        let mut corrections = 0u32;
        while qhat > u128::from(u64::MAX)
            || qhat * vnext > ((rhat << 64) | u128::from(un[j + n - 2]))
        {
            qhat -= 1;
            rhat += vtop;
            corrections += 1;
            debug_assert!(corrections <= 2, "limbs::divrem: an unnormalized divisor");
            if rhat > u128::from(u64::MAX) {
                break;
            }
        }
        // Multiply and subtract: un[j..=j+n] -= qhat * vn.
        let mut borrow = 0i128;
        let mut carry = 0u128;
        for i in 0..n {
            let p = qhat * u128::from(vn[i]) + carry;
            carry = p >> 64;
            let t = i128::from(un[i + j]) - i128::from(p as u64) + borrow;
            un[i + j] = t as u64;
            borrow = t >> 64;
        }
        let t = i128::from(un[j + n]) - carry as i128 + borrow;
        un[j + n] = t as u64;
        if t < 0 {
            // qhat was one too large: add the divisor back.
            qhat -= 1;
            let mut c = 0u128;
            for i in 0..n {
                let s = u128::from(un[i + j]) + u128::from(vn[i]) + c;
                un[i + j] = s as u64;
                c = s >> 64;
            }
            un[j + n] = un[j + n].wrapping_add(c as u64);
        }
        q[j] = qhat as u64;
    }
    // The remainder is un[..n] shifted back.
    let rn = shr(&un[..n], shift, r);
    (normalized_len(&q[..=m]), rn)
}

/// `out = gcd(a, b)` (`mpz_gcd`: never negative, `gcd(0, b) = b`).  `out`
/// holds at least `max(|a|, |b|)` limbs.  Euclid's algorithm over [`divrem`].
pub fn gcd(a: &[u64], b: &[u64], out: &mut [u64]) -> usize {
    let cap = a.len().max(b.len()).max(1);
    let mut x_s = super::Scratch::new(cap);
    let mut y_s = super::Scratch::new(cap);
    let mut t_s = super::Scratch::new(cap);
    let mut q_s = super::Scratch::new(cap + 1);
    let (x, y, t, q) = (x_s.slice(), y_s.slice(), t_s.slice(), q_s.slice());
    x[..a.len()].copy_from_slice(a);
    y[..b.len()].copy_from_slice(b);
    let (mut xn, mut yn) = (a.len(), b.len());
    while yn != 0 {
        t.fill(0);
        q.fill(0);
        let (_, rn) = divrem(&x[..xn], &y[..yn], q, t);
        x.copy_from_slice(y);
        xn = yn;
        y.fill(0);
        y[..rn].copy_from_slice(&t[..rn]);
        yn = rn;
    }
    out[..xn].copy_from_slice(&x[..xn]);
    xn
}

/// `out = a ^ e` by repeated squaring.  `out` holds enough limbs for the
/// result: `(log2(a) + 1) * e / 64 + 1` suffices.
pub fn pow(a: &[u64], e: usize, out: &mut [u64]) -> usize {
    if e == 0 {
        out[0] = 1;
        return 1;
    }
    if a.is_empty() {
        return 0;
    }
    let cap = out.len();
    let mut base_s = super::Scratch::new(cap);
    let mut tmp_s = super::Scratch::new(2 * cap);
    let (base, tmp) = (base_s.slice(), tmp_s.slice());
    base[..a.len()].copy_from_slice(a);
    let mut bn = a.len();
    out.fill(0);
    out[0] = 1;
    let mut rn = 1;
    let mut e = e;
    loop {
        if e & 1 == 1 {
            tmp.fill(0);
            let n = mul(&out[..rn], &base[..bn], tmp);
            out.fill(0);
            out[..n].copy_from_slice(&tmp[..n]);
            rn = n;
        }
        e >>= 1;
        if e == 0 {
            break;
        }
        tmp.fill(0);
        let n = mul(&base[..bn], &base[..bn], tmp);
        if n > cap {
            // The square outgrew the result's bound; only reachable if the
            // result itself would, which the caller's bound rules out.
            super::super::fatal("Nat.pow: result bound exceeded");
        }
        base.fill(0);
        base[..n].copy_from_slice(&tmp[..n]);
        bn = n;
    }
    rn
}

/// Parses decimal `digits` into `out`, which holds `len / 19 + 1` limbs,
/// zeroed.  `None` for an empty string or a non-digit.
#[must_use]
pub fn parse_decimal(digits: &[u8], out: &mut [u64]) -> Option<usize> {
    if digits.is_empty() {
        return None;
    }
    let mut len = 0usize;
    for chunk in digits.chunks(19) {
        let mut v = 0u64;
        for &c in chunk {
            if !c.is_ascii_digit() {
                return None;
            }
            v = v * 10 + u64::from(c - b'0');
        }
        let scale = 10u64.pow(chunk.len() as u32);
        // out = out * scale + v, in place.
        let mut carry = u128::from(v);
        for limb in out.iter_mut().take(len) {
            let t = u128::from(*limb) * u128::from(scale) + carry;
            *limb = t as u64;
            carry = t >> 64;
        }
        if carry != 0 {
            out[len] = carry as u64;
            len += 1;
        }
    }
    Some(normalized_len(&out[..len]))
}
