//! Truncated power series over F_2 stored as bitsets (bit n of word n/64 is the coefficient of q^n).
//! Built for parity questions on eta products: mod 2, f_m = prod (1 - q^{mk}) is the pentagonal
//! theta series sum_k q^{m k(3k-1)/2}, f_m^3 is the triangular series sum_{k>=0} q^{m k(k+1)/2},
//! and f_1^t = prod over the binary digits 2^i of t of f_{2^i}.
//!
//! Products are "dense times sparse": XOR of shifted copies of the dense factor, parallel over
//! blocks of output words (rayon). Cost O(len * #terms(sparse) / 64) word operations.
//! Exactness is trivial (F_2), the only risk is indexing; `mul_naive` is the reference used in tests.

use rayon::prelude::*;

/// Bitset series truncated at q^len (coefficients of q^0 .. q^{len-1}).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ser2 {
    pub len: usize,
    pub w: Vec<u64>,
}

impl Ser2 {
    pub fn zero(len: usize) -> Self {
        Ser2 { len, w: vec![0u64; (len + 63) / 64] }
    }
    pub fn one(len: usize) -> Self {
        let mut s = Self::zero(len);
        if len > 0 {
            s.w[0] = 1;
        }
        s
    }
    #[inline(always)]
    pub fn get(&self, n: usize) -> bool {
        n < self.len && (self.w[n >> 6] >> (n & 63)) & 1 == 1
    }
    #[inline(always)]
    pub fn flip(&mut self, n: usize) {
        if n < self.len {
            self.w[n >> 6] ^= 1u64 << (n & 63);
        }
    }
    /// Sparse series from a list of exponents (each exponent toggles its bit, so repeated
    /// exponents cancel as they should mod 2).
    pub fn from_exps(exps: &[usize], len: usize) -> Self {
        let mut s = Self::zero(len);
        for &e in exps {
            s.flip(e);
        }
        s
    }
    /// Exponents with coefficient 1, increasing.
    pub fn support(&self) -> Vec<usize> {
        let mut v = Vec::new();
        for (i, &x) in self.w.iter().enumerate() {
            let mut y = x;
            while y != 0 {
                let b = y.trailing_zeros() as usize;
                let n = (i << 6) | b;
                if n < self.len {
                    v.push(n);
                }
                y &= y - 1;
            }
        }
        v
    }
    pub fn count_ones(&self) -> u64 {
        self.w.par_iter().map(|x| x.count_ones() as u64).sum()
    }
    fn clear_tail(&mut self) {
        let r = self.len & 63;
        if r != 0 {
            let last = self.w.len() - 1;
            self.w[last] &= (1u64 << r) - 1;
        }
    }
}

/// Exponents of f_m mod 2 below len: m k(3k-1)/2 for k in Z (distinct, each with coefficient 1).
pub fn pent_exps(m: usize, len: usize) -> Vec<usize> {
    let mut v = Vec::new();
    let mut k: i64 = 0;
    loop {
        // k >= 0 gives k(3k-1)/2 and k(3k+1)/2 (the latter is the value at -k)
        let a = (k * (3 * k - 1) / 2) as usize * m;
        if a >= len {
            break;
        }
        v.push(a);
        if k > 0 {
            let b = (k * (3 * k + 1) / 2) as usize * m;
            if b < len {
                v.push(b);
            }
        }
        k += 1;
    }
    v.sort_unstable();
    v
}

/// Exponents of f_m^3 mod 2 below len: m k(k+1)/2 for k >= 0 (Jacobi: f_1^3 = sum (-1)^k (2k+1) q^{k(k+1)/2}).
pub fn tri_exps(m: usize, len: usize) -> Vec<usize> {
    let mut v = Vec::new();
    let mut k: usize = 0;
    loop {
        let a = k * (k + 1) / 2 * m;
        if a >= len {
            break;
        }
        v.push(a);
        k += 1;
    }
    v
}

/// Product of a dense series by a sparse one given by its exponents (each toggling), truncated
/// at a.len. Parallel over blocks of output words.
pub fn mul_sparse(a: &Ser2, exps: &[usize]) -> Ser2 {
    let len = a.len;
    let nw = a.w.len();
    let mut out = Ser2::zero(len);
    const BLK: usize = 2048;
    out.w.par_chunks_mut(BLK).enumerate().for_each(|(bi, chunk)| {
        let w0 = bi * BLK;
        let w1 = w0 + chunk.len();
        for &e in exps {
            if e >= len {
                continue;
            }
            let q = e >> 6;
            let r = (e & 63) as u32;
            // out[w] ^= (a << e)[w] = (a[w-q] << r) | (a[w-q-1] >> (64-r))
            let lo = w0.max(q);
            if lo >= w1 {
                continue;
            }
            if r == 0 {
                for w in lo..w1 {
                    chunk[w - w0] ^= a.w[w - q];
                }
            } else {
                let rr = 64 - r;
                // first word may lack the carry-in from a[w-q-1] when w == q
                let mut w = lo;
                if w == q {
                    chunk[w - w0] ^= a.w[0] << r;
                    w += 1;
                }
                while w < w1 {
                    let s = w - q;
                    chunk[w - w0] ^= (a.w[s] << r) | (a.w[s - 1] >> rr);
                    w += 1;
                }
            }
        }
    });
    let _ = nw;
    out.clear_tail();
    out
}

/// Product of two sparse series given by exponent lists (every pair toggles one bit).
pub fn mul_sparse_sparse(e1: &[usize], e2: &[usize], len: usize) -> Ser2 {
    let mut out = Ser2::zero(len);
    for &x in e1 {
        if x >= len {
            break;
        }
        for &y in e2 {
            let s = x + y;
            if s >= len {
                break;
            }
            out.w[s >> 6] ^= 1u64 << (s & 63);
        }
    }
    out
}

/// Reference product (quadratic), for tests.
pub fn mul_naive(a: &Ser2, b: &Ser2) -> Ser2 {
    let len = a.len.min(b.len);
    let mut out = Ser2::zero(len);
    let sb = b.support();
    for i in a.support() {
        for &j in &sb {
            if i + j < len {
                out.flip(i + j);
            } else {
                break;
            }
        }
    }
    out
}

/// Factorisation of f_1^t mod 2 into sparse theta factors: scan the binary digits of t from
/// the bottom; two adjacent digits 2^i + 2^{i+1} give f_{2^i}^3 (triangular), a lone digit
/// gives f_{2^i} (pentagonal). Returns (m, is_triangular) pairs.
pub fn eta_power_factors(t: u64) -> Vec<(usize, bool)> {
    let mut f = Vec::new();
    let mut i = 0u32;
    while i < 64 && (t >> i) != 0 {
        if (t >> i) & 1 == 1 {
            if (t >> (i + 1)) & 1 == 1 {
                f.push((1usize << i, true));
                i += 2;
                continue;
            }
            f.push((1usize << i, false));
        }
        i += 1;
    }
    f
}

fn factor_exps(m: usize, tri: bool, len: usize) -> Vec<usize> {
    if tri { tri_exps(m, len) } else { pent_exps(m, len) }
}

/// f_1^t mod 2 truncated at q^len. Sparsest factors are multiplied first.
pub fn eta_power(t: u64, len: usize) -> Ser2 {
    let mut fs: Vec<Vec<usize>> = eta_power_factors(t).into_iter().map(|(m, tr)| factor_exps(m, tr, len)).collect();
    if fs.is_empty() {
        return Ser2::one(len);
    }
    fs.sort_by_key(|v| v.len());
    if fs.len() == 1 {
        return Ser2::from_exps(&fs[0], len);
    }
    let mut acc = mul_sparse_sparse(&fs[0], &fs[1], len);
    for e in &fs[2..] {
        acc = mul_sparse(&acc, e);
    }
    acc
}

/// f_1^t mod 2 by repeated multiplication with f_1 (slow reference for tests).
pub fn eta_power_naive(t: u64, len: usize) -> Ser2 {
    let f1 = Ser2::from_exps(&pent_exps(1, len), len);
    let mut acc = Ser2::one(len);
    for _ in 0..t {
        acc = mul_naive(&acc, &f1);
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pentagonal_and_triangular() {
        // f_1 = 1 - q - q^2 + q^5 + q^7 - q^12 - q^15 + ...
        assert_eq!(pent_exps(1, 30), vec![0, 1, 2, 5, 7, 12, 15, 22, 26]);
        assert_eq!(tri_exps(1, 30), vec![0, 1, 3, 6, 10, 15, 21, 28]);
        // f_1^3 = f_1 * f_2 mod 2
        let len = 2000;
        let a = mul_sparse_sparse(&pent_exps(1, len), &pent_exps(2, len), len);
        assert_eq!(a, Ser2::from_exps(&tri_exps(1, len), len));
    }

    #[test]
    fn eta_powers_against_naive() {
        let len = 1500;
        for t in 1..=40u64 {
            assert_eq!(eta_power(t, len), eta_power_naive(t, len), "t = {}", t);
        }
    }

    #[test]
    fn mul_sparse_against_naive() {
        // lengths not multiple of 64, shifts with r = 0 and r != 0, crossing block borders
        for &len in &[1usize, 63, 64, 65, 200, 4097, 64 * 2048 + 77, 3 * 64 * 2048 + 5] {
            let a = Ser2::from_exps(&pent_exps(1, len), len);
            let mut exps = tri_exps(3, len);
            exps.push(64.min(len.saturating_sub(1)));
            exps.push(128.min(len.saturating_sub(1)));
            exps.sort_unstable();
            exps.dedup();
            let b = Ser2::from_exps(&exps, len);
            assert_eq!(mul_sparse(&a, &exps), mul_naive(&a, &b), "len = {}", len);
        }
    }
}
