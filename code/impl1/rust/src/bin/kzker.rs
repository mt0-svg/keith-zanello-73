//! Which odd t < 2^B satisfy T_p G = 0 (mod 2), for G = G_t = eta(24z)^t (mode "eta") or
//! G = Delta^t (mode "delta", level 1)?
//!
//! Test used. T_p preserves V_s = span{G_{s+24j}} (class s -> ps mod 24) and lowers the index j
//! (checked by kzhecke on small cases), and the G_{s'+24j'} are in echelon form with leading exponent
//! m = s' + 24 j'. Hence T_p G_t = 0 iff (T_p G_t)(m) = 0 for all m <= t + MARGIN in the class of p t.
//! We check m up to t + 24*MARGIN_J; a nonzero coefficient above t would contradict the triangular
//! structure and is reported as "ANOMALY". Same for Delta^u with exponents m = u mod 8 (Nicolas-Serre).
//!
//! Series are built by a depth first recursion over the binary digits of t, from the top digit down,
//! so the partial products of the high digits are shared.
//!
//! Usage: kzker MODE P B   (MODE = eta | delta). Prints the t with T_p G_t = 0, one per line, then the t
//! for which only the evenness condition (a(pm) = 0 for p not dividing m, m <= t + 24*MARGIN_J) holds.
use kz73::ser2::{mul_sparse, pent_exps, Ser2};
use std::env;

const MARGIN_J: u64 = 3;

struct Ctx {
    p: u64,
    eta: bool,
    len: usize,     // series length in the variable N (eta) or n (delta)
    factors: Vec<Vec<usize>>, // exponents of the theta factor of digit i
    out: Vec<u64>,
    anomalies: Vec<u64>,
    even_only: Vec<u64>, // evenness holds on the range but T_p G_t != 0
}

// coefficient a(m) of G_t in the variable m (eta: m = 24N + t; delta: m = n)
fn coef(ctx: &Ctx, g: &Ser2, t: u64, m: u64) -> bool {
    if ctx.eta {
        if m < t || (m - t) % 24 != 0 {
            return false;
        }
        let n = ((m - t) / 24) as usize;
        assert!(n < ctx.len, "series too short");
        g.get(n)
    } else {
        let n = m as usize;
        assert!(n < ctx.len, "series too short");
        g.get(n)
    }
}

fn test(ctx: &mut Ctx, g: &Ser2, t: u64) {
    let p = ctx.p;
    let (modu, step) = if ctx.eta { (24u64, 24u64) } else { (8u64, 8u64) };
    let cls = (p * t) % modu;
    let top = t + step * MARGIN_J;
    let mut m = cls;
    let mut zero = true;
    let mut even = true; // evenness condition a(pm) = 0 for p not dividing m, on the tested range
    let mut anomaly = false;
    while m <= top {
        if m > 0 {
            let mut b = coef(ctx, g, t, p * m);
            if m % p == 0 {
                b ^= coef(ctx, g, t, m / p);
            }
            if b && m % p != 0 {
                even = false;
            }
            if b {
                if m <= t {
                    zero = false;
                } else {
                    anomaly = true;
                }
            }
        }
        m += step;
    }
    // an anomaly only matters when every coefficient up to t vanishes
    if anomaly && zero {
        ctx.anomalies.push(t);
    }
    if zero && !anomaly {
        ctx.out.push(t);
    } else if even {
        ctx.even_only.push(t);
    }
}

// digits >= i are fixed (partial product g, value t_hi); decide digit i-1 ... 0; digit 0 forced to 1
fn dfs(ctx: &mut Ctx, g: &Ser2, i: usize, t_hi: u64) {
    if i == 1 {
        let h = mul_sparse(g, &ctx.factors[0].clone());
        let t = t_hi | 1;
        test(ctx, &h, t);
        return;
    }
    let d = i - 1;
    // digit d = 0
    dfs(ctx, g, d, t_hi);
    // digit d = 1
    let fac = ctx.factors[d].clone();
    let h = mul_sparse(g, &fac);
    dfs(ctx, &h, d, t_hi | (1u64 << d));
}

// low digits first: digits < i fixed (digit 0 = 1), partial product g; the dense factors of the low
// digits are shared by many leaves, the leaves only multiply by sparse high-digit factors
fn dfs_low(ctx: &mut Ctx, g: &Ser2, i: usize, t_lo: u64, bits: usize) {
    if i == bits {
        test(ctx, g, t_lo);
        return;
    }
    dfs_low(ctx, g, i + 1, t_lo, bits);
    let fac = ctx.factors[i].clone();
    let h = mul_sparse(g, &fac);
    dfs_low(ctx, &h, i + 1, t_lo | (1u64 << i), bits);
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 4 {
        eprintln!("usage: kzker eta|delta P B");
        std::process::exit(1);
    }
    let eta = args[1] == "eta";
    let p: u64 = args[2].parse().unwrap();
    let bits: usize = args[3].parse().unwrap();
    let tmax = 1u64 << bits;
    // need a(p m) for m <= tmax + 24*MARGIN_J (eta: N = (p m - t)/24), or n = p m (delta)
    let len = if eta {
        ((p * (tmax + 24 * MARGIN_J + 24)) / 24 + 2) as usize
    } else {
        (p * (tmax + 8 * MARGIN_J + 8) + 2) as usize
    };
    let factors: Vec<Vec<usize>> = (0..bits)
        .map(|i| {
            if eta {
                pent_exps(1usize << i, len)
            } else {
                // Delta(q^{2^i}) = sum_{n odd} q^{2^i n^2}
                let mut v = Vec::new();
                let mut n = 1usize;
                while (n * n) << i < len {
                    v.push((n * n) << i);
                    n += 2;
                }
                v
            }
        })
        .collect();
    let mut ctx = Ctx { p, eta, len, factors, out: Vec::new(), anomalies: Vec::new(), even_only: Vec::new() };
    println!("# kzker mode={} p={} t < 2^{} len={}", args[1], p, bits, len);
    // KZ_FIRST=old: original top-digit-first recursion (for cross-checks)
    if env::var("KZ_FIRST").map(|v| v == "old").unwrap_or(false) {
        let one = Ser2::one(len);
        dfs(&mut ctx, &one, bits, 0);
    } else {
        let root = Ser2::from_exps(&ctx.factors[0].clone(), len);
        dfs_low(&mut ctx, &root, 1, 1, bits);
    }
    let mut out = ctx.out.clone();
    out.sort_unstable();
    for t in &out {
        println!("{}", t);
    }
    if !ctx.even_only.is_empty() {
        let mut e = ctx.even_only.clone();
        e.sort_unstable();
        println!("# EVEN_ONLY (evenness on the range, T_p G_t != 0): {:?}", e);
    }
    if !ctx.anomalies.is_empty() {
        println!("# ANOMALY at t = {:?}", ctx.anomalies);
    }
    eprintln!("p={} mode={} bits={}: {} values", p, args[1], bits, out.len());
}
