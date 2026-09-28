//! Finiteness certificate for the set of odd t with f_1^t (p,r)-even for some r, at a fixed prime p.
//! Lemmas and notation: the paper, paper/main.tex, Sections 3 to 6.
//!
//! Steps (all exact over F_2; any failed check is printed and makes the final verdict FAIL):
//!  1. Goodness (Lemma 4, Sturm): for each t in GOOD, T_p G_t has zero coefficients for m <= 48(t+1).
//!  2. Sparse points 1 and 3 (Lemma 3): K0 from the size condition, then for every e in <2> mod p^2
//!     and every odd w mod 2^j, special indices give a pair in every class.
//!  3. Tree over odd 2-adic T starting at level KSTART: a node is settled when closed (Lemma 1),
//!     or when it is a good t >= 5 satisfying (i),(ii) (Lemma 2), or when it is 1 or 3 at level >= K0.
//!     Nodes still open at level MAXDEPTH are printed.
//!
//! Usage: kztree P KSTART MAXDEPTH KAPPA MU GOOD(comma separated)
use kz73::ser2::{eta_power, mul_sparse, pent_exps, tri_exps, Ser2};
use rayon::prelude::*;
use std::collections::HashSet;
use std::env;

fn modp(a: i64, m: i64) -> usize {
    (((a % m) + m) % m) as usize
}

/// For each class rho mod p: does F (indices < len) have odd coefficients in two classes mod p^2 ?
fn pairs(f: &Ser2, p: usize) -> Vec<bool> {
    let p2 = p * p;
    let mut mark = vec![false; p2];
    // only indices N >= p^2: the progression p^2 n + k p + r (n >= 0) starts above r, and r < p^2
    for n in f.support() {
        if n >= p2 {
            mark[n % p2] = true;
        }
    }
    (0..p).map(|rho| (0..p).filter(|&i| mark[rho + i * p]).count() >= 2).collect()
}

/// Step 1: T_p G_t = 0 mod 2 checked for m <= 48(t+1) (Sturm bound, weight (t+1)/2, level 576).
fn sturm_good(p: u64, t: u64) -> bool {
    let bound = 48 * (t + 1);
    // need a(p m) for m <= bound: N = (p m - t)/24
    let len = ((p * bound) / 24 + 2) as usize;
    let g = eta_power(t, len);
    let a = |m: u64| -> bool { m >= t && (m - t) % 24 == 0 && g.get(((m - t) / 24) as usize) };
    for m in 1..=bound {
        let mut b = a(p * m);
        if m % p == 0 {
            b ^= a(m / p);
        }
        if b {
            return false;
        }
    }
    true
}

/// Lemma 2 conditions at level k for a good t (t < 2^k).
fn lemma2_ok(f: &Ser2, p: usize, t: u64) -> bool {
    let p2 = p * p;
    let rho_t = modp(-(t as i64) * inv24(p as i64, p as i64) as i64, p as i64);
    let pr = pairs(f, p);
    let cond_i = (0..p).all(|rho| rho == rho_t || pr[rho]);
    let cond_ii = f.support().iter().any(|&n| n >= p2 && n % p == rho_t);
    let _ = p2;
    cond_i && cond_ii
}

fn inv24(p: i64, m: i64) -> i64 {
    // inverse of 24 mod m (m a power of p), by extended Euclid
    let (mut a, mut b, mut x0, mut x1) = (24i64.rem_euclid(m), m, 1i64, 0i64);
    while b != 0 {
        let q = a / b;
        let t = a - q * b;
        a = b;
        b = t;
        let t = x0 - q * x1;
        x0 = x1;
        x1 = t;
    }
    let _ = p;
    x0.rem_euclid(m)
}

/// Least K >= 1 from which the size condition of Lemma 3 holds for every larger K.
/// Pentagonal (tri = false) or triangular (tri = true). Exact integer test: with X = 2^K,
/// the left side is bounded below by a quadratic h(X) (pentagonal: L >= (2X - 3 kappa - 1)/3 and
/// (3L^2 - L)/2 increasing for L >= 1/6, so 6 h = (2X - a)(2X - a - 1) - 6 mu X - 3(3 kappa^2 + kappa),
/// a = 3 kappa + 1; triangular: L = 2X - kappa - 1 exactly, 2 h = (2X - kappa - 1)(2X - kappa)
/// - 2 mu X - kappa(kappa + 1)). h has positive leading coefficient, so h(X0) > 0 and h'(X0) > 0
/// give h(X) > 0 for all X >= X0, hence the size condition for all K >= K0.
fn sparse_k0(kappa: i64, mu: i64, tri: bool) -> u32 {
    let (kap, m) = (kappa as i128, mu as i128);
    for k0 in 1..62u32 {
        let x = 1i128 << k0;
        let ok = if tri {
            let l = 2 * x - kap - 1;
            let h2 = l * (l + 1) - 2 * m * x - kap * (kap + 1);
            let dh = 4 * x - 2 * kap - 1 - m; // h'(X)
            l >= 1 && h2 > 0 && dh > 0
        } else {
            let a = 3 * kap + 1;
            let num = 2 * x - a; // 3y, y the real lower bound of L
            let h6 = num * (num - 1) - 6 * m * x - 3 * (3 * kap * kap + kap);
            let dh6 = 8 * x - 4 * a - 2 - 6 * m; // 6 h'(X)
            // y >= 1/6 (so that (3L^2 - L)/2 is increasing on [y, L]) and L >= 1
            6 * num >= 3 && num >= 1 && h6 > 0 && dh6 > 0
        };
        if ok {
            return k0;
        }
    }
    panic!("no K0");
}

/// Step 2 for tau in {1, 3}: returns the list of (e, w) failures.
fn sparse_check(p: usize, tau: u64, kappa: i64, mu: usize, mmin: usize) -> Vec<(usize, u64)> {
    let p2 = p * p;
    let tri = tau == 3;
    // small theta exponents P_s (pentagonal, |k| <= kappa) or T_s (triangular, 0 <= k <= kappa), mod p^2
    let small: Vec<usize> = if tri {
        (0..=kappa).map(|k| modp(k * (k + 1) / 2, p2 as i64)).collect()
    } else {
        (-kappa..=kappa).map(|k| modp(k * (3 * k - 1) / 2, p2 as i64)).collect()
    };
    // cyclic group generated by 2 mod p^2
    let mut es = Vec::new();
    let mut e = 1usize;
    loop {
        es.push(e);
        e = e * 2 % p2;
        if e == 1 {
            break;
        }
    }
    let mut j = 0;
    while (1usize << j) <= mu {
        j += 1;
    }
    let ws: Vec<u64> = (0..(1u64 << j)).filter(|w| w % 2 == 1).collect();
    let sw: Vec<Vec<usize>> = ws
        .iter()
        .map(|&w| {
            let f = eta_power(w, mu + 1);
            f.support()
        })
        .collect();
    // Reduced check (sufficient): two small exponents s, s' in the same class mod p but distinct mod p^2,
    // used with the same M, give indices distinct mod p^2 whatever 2^K is; so only e mod p matters.
    let mut dcls = vec![false; p];
    {
        let mut seen: Vec<Vec<usize>> = vec![Vec::new(); p];
        for &s in &small {
            if !seen[s % p].contains(&s) {
                seen[s % p].push(s);
            }
        }
        for c in 0..p {
            dcls[c] = seen[c].len() >= 2;
        }
    }
    let mut eps: Vec<usize> = es.iter().map(|&e| e % p).collect();
    eps.sort_unstable();
    eps.dedup();
    // rot[s] = bitset of the classes (c + s) mod p with dcls[c]
    let nwp = p.div_ceil(64);
    let rot: Vec<Vec<u64>> = (0..p)
        .map(|s| {
            let mut v = vec![0u64; nwp];
            for c in 0..p {
                if dcls[c] {
                    let x = (c + s) % p;
                    v[x >> 6] |= 1u64 << (x & 63);
                }
            }
            v
        })
        .collect();
    let mut full = vec![0u64; nwp];
    for x in 0..p {
        full[x >> 6] |= 1u64 << (x & 63);
    }
    let red_fail: Vec<(usize, usize)> = eps
        .par_iter()
        .flat_map(|&ep| {
            let mut out = Vec::new();
            for (wi, _) in ws.iter().enumerate() {
                let mut cov = vec![0u64; nwp];
                let mut ok = false;
                for &m in &sw[wi] {
                    if m < mmin {
                        continue;
                    }
                    let r = &rot[ep * m % p];
                    for i in 0..nwp {
                        cov[i] |= r[i];
                    }
                    if cov == full {
                        ok = true;
                        break;
                    }
                }
                if !ok {
                    out.push((ep, wi));
                }
            }
            out
        })
        .collect();
    // full check only for the (e, w) above a reduced failure
    let todo: Vec<(usize, usize)> = es
        .iter()
        .flat_map(|&e| red_fail.iter().filter(move |&&(ep, _)| ep == e % p).map(move |&(_, wi)| (e, wi)))
        .collect();
    eprintln!("sparse tau={}: {} values of e mod p, reduced failures {}, full checks {}", tau, eps.len(), red_fail.len(), todo.len());
    let fails: Vec<(usize, u64)> = todo
        .par_iter()
        .flat_map(|&(e, wi0)| {
            let mut out = Vec::new();
            for (wi, &w) in ws.iter().enumerate().filter(|(i, _)| *i == wi0) {
                let mut mark = vec![false; p2];
                for &m in &sw[wi] {
                    if m < mmin {
                        continue; // special index 2^K M + s >= 2^K0 M >= p^2 needs M >= mmin
                    }
                    let base = e * m % p2;
                    for &s in &small {
                        mark[(base + s) % p2] = true;
                    }
                }
                let ok = (0..p).all(|rho| (0..p).filter(|&i| mark[rho + i * p]).count() >= 2);
                if !ok {
                    out.push((e, w));
                }
            }
            out
        })
        .collect();
    fails
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 7 {
        eprintln!("usage: kztree P KSTART MAXDEPTH KAPPA MU GOOD");
        std::process::exit(1);
    }
    let p: u64 = args[1].parse().unwrap();
    let kstart: u32 = args[2].parse().unwrap();
    let maxdepth: u32 = args[3].parse().unwrap();
    let kappa: i64 = args[4].parse().unwrap();
    let mu: usize = args[5].parse().unwrap();
    let good: Vec<u64> = args[6].split(',').map(|s| s.parse().unwrap()).collect();
    let goodset: HashSet<u64> = good.iter().cloned().collect();
    let pu = p as usize;
    let mut verdict_ok = true;
    let t_start = std::time::Instant::now();
    println!("# kztree p={} kstart={} maxdepth={} kappa={} mu={} good={:?}", p, kstart, maxdepth, kappa, mu, good);
    let _ = pent_exps(1, 1);

    // Step 1
    for &t in &good {
        if t >= 5 {
            let ok = sturm_good(p, t);
            println!("step1 sturm t={} T_p G_t = 0 up to m <= {}: {}", t, 48 * (t + 1), ok);
            if !ok {
                verdict_ok = false;
            }
        }
    }

    // Step 2
    let mut k0s = [0u32; 2];
    for (i, &tau) in [1u64, 3u64].iter().enumerate() {
        let k0 = sparse_k0(kappa, mu as i64, tau == 3);
        let mmin = (pu * pu + (1usize << k0) - 1) >> k0;
        let fails = sparse_check(pu, tau, kappa, mu, mmin);
        println!("step2 sparse tau={} K0={} Mmin={} failures(e,w)={} {:?} [{:.1} s]", tau, k0, mmin, fails.len(), &fails[..fails.len().min(20)], t_start.elapsed().as_secs_f64());
        if !fails.is_empty() {
            verdict_ok = false;
        }
        k0s[i] = k0;
    }

    // Step 3
    let classify = |tau: u64, k: u32, f: &Ser2| -> u8 {
        // 0 = split, 1 = closed, 2 = lemma 2, 3 = sparse
        // Lemma 3 covers every T = 1 + 2^K w (resp. 3 + 2^K w), K >= K0, w odd: all T = 1 mod 2^K0
        // (resp. 3 mod 2^K0) except T = 1 (resp. 3). A node inside such a ball is settled.
        if (k >= k0s[0] && tau % (1u64 << k0s[0]) == 1) || (k >= k0s[1] && tau % (1u64 << k0s[1]) == 3) {
            return 3u8;
        }
        if closed_fast(f, pu) {
            return 1u8;
        }
        if tau >= 5 && goodset.contains(&tau) && lemma2_ok(f, pu, tau) {
            return 2u8;
        }
        0u8
    };
    // first level: every odd tau < 2^kstart, by a depth first product over the binary digits
    // KZ_FIRST=old selects the original top-digit-first product (for cross-checks)
    let first: Vec<(u64, u8)> = if env::var("KZ_FIRST").map(|v| v == "old").unwrap_or(false) {
        first_level(kstart, &classify)
    } else {
        first_level_low(kstart, &classify)
    };
    let mut level: Vec<u64> = (0..(1u64 << kstart)).filter(|x| x % 2 == 1).collect();
    let mut k = kstart;
    let mut first_opt = Some(first);
    let mut open_final = Vec::new();
    let mut lemma2_used: Vec<(u64, u32)> = Vec::new();
    while !level.is_empty() {
        let res: Vec<(u64, u8)> = if let Some(fr) = first_opt.take() {
            fr
        } else {
            level
                .par_iter()
                .map(|&tau| {
                    let f = eta_power(tau, 1usize << k);
                    (tau, classify(tau, k, &f))
                })
                .collect()
        };
        let mut next = Vec::new();
        let (mut nc, mut n2, mut ns) = (0, 0, 0);
        for (tau, r) in res {
            match r {
                1 => nc += 1,
                2 => {
                    n2 += 1;
                    lemma2_used.push((tau, k));
                }
                3 => ns += 1,
                _ => {
                    if k >= maxdepth {
                        open_final.push(tau);
                    } else {
                        next.push(tau);
                        next.push(tau + (1u64 << k));
                    }
                }
            }
        }
        let opened = next.len() / 2;
        let shown: Vec<u64> = next.iter().filter(|&&x| x < (1u64 << k)).take(40).cloned().collect();
        println!("step3 level {}: [{:.1} s] nodes {}, closed {}, lemma2 {}, sparse {}, split {} {:?}", k, t_start.elapsed().as_secs_f64(), nc + n2 + ns + opened + if k >= maxdepth { open_final.len() } else { 0 }, nc, n2, ns, opened, shown);
        level = next;
        k += 1;
    }
    lemma2_used.sort();
    println!("lemma2 centers (t, level): {:?}", lemma2_used);
    let centers: HashSet<u64> = lemma2_used.iter().map(|x| x.0).collect();
    for &t in &good {
        if t >= 5 && !centers.contains(&t) {
            println!("note: good t={} was not used as a Lemma 2 center", t);
        }
    }
    if !open_final.is_empty() {
        println!("OPEN at maxdepth {}: {:?}", maxdepth, &open_final[..open_final.len().min(100)]);
        verdict_ok = false;
    }
    println!("VERDICT: {}", if verdict_ok { "PASS (good odd 2-adic integers = the listed ones)" } else { "FAIL" });
}

/// All odd tau < 2^k with their classification, f_1^tau mod q^{2^k} built by a depth first
/// product over the binary digits (top digit first), shared prefixes, parallel over the top digits.
fn first_level<F: Fn(u64, u32, &Ser2) -> u8 + Sync>(k: u32, classify: &F) -> Vec<(u64, u8)> {
    let len = 1usize << k;
    let facs: Vec<Vec<usize>> = (0..k).map(|i| pent_exps(1usize << i, len)).collect();
    let leaf1 = pent_exps(1, len); // tau = 1 mod 4: remaining factor f_1
    let leaf3 = tri_exps(1, len); // tau = 3 mod 4: remaining factor f_1 f_2 = f_1^3
    let ku = k as usize;
    let d = ku.saturating_sub(2).min(8); // parallel over the digits k-1 .. k-d
    let prefixes: Vec<u64> = (0..(1u64 << d)).collect();
    prefixes
        .par_iter()
        .flat_map(|&pre| {
            // digits k-1 .. k-d from pre
            let mut g: Option<Ser2> = None;
            let mut hi = 0u64;
            for idx in 0..d {
                let bit = ku - 1 - idx;
                if (pre >> (d - 1 - idx)) & 1 == 1 {
                    hi |= 1u64 << bit;
                    g = Some(match g {
                        None => Ser2::from_exps(&facs[bit], len),
                        Some(h) => mul_sparse(&h, &facs[bit]),
                    });
                }
            }
            let g = g.unwrap_or_else(|| Ser2::one(len));
            let mut out = Vec::new();
            dfs_digits(&g, ku - d, hi, k, &facs, &leaf1, &leaf3, classify, &mut out);
            out
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn dfs_digits<F: Fn(u64, u32, &Ser2) -> u8>(
    g: &Ser2,
    i: usize, // digits >= i fixed
    hi: u64,
    k: u32,
    facs: &[Vec<usize>],
    leaf1: &[usize],
    leaf3: &[usize],
    classify: &F,
    out: &mut Vec<(u64, u8)>,
) {
    if i <= 2 {
        // digits 1, 0: tau = hi + 1 or hi + 3
        for (low, leaf) in [(1u64, leaf1), (3u64, leaf3)] {
            let f = mul_sparse(g, leaf);
            let tau = hi | low;
            out.push((tau, classify(tau, k, &f)));
        }
        return;
    }
    let bit = i - 1;
    dfs_digits(g, bit, hi, k, facs, leaf1, leaf3, classify, out);
    let h = mul_sparse(g, &facs[bit]);
    dfs_digits(&h, bit, hi | (1u64 << bit), k, facs, leaf1, leaf3, classify, out);
}

/// Same result as `first_level`, with the low digits at the root of the depth first product:
/// the dense factors f_1, f_2, f_4, ... are shared by many leaves and the leaves only multiply
/// by the sparse f_{2^i} with i large. Parallel over digits 1 .. d (d <= 8).
fn first_level_low<F: Fn(u64, u32, &Ser2) -> u8 + Sync>(k: u32, classify: &F) -> Vec<(u64, u8)> {
    let len = 1usize << k;
    let ku = k as usize;
    let facs: Vec<Vec<usize>> = (0..k).map(|i| pent_exps(1usize << i, len)).collect();
    let d = (ku - 1).min(8); // digits 1..=d chosen by the parallel prefix
    let prefixes: Vec<u64> = (0..(1u64 << d)).collect();
    prefixes
        .par_iter()
        .flat_map(|&pre| {
            let mut g = Ser2::from_exps(&facs[0], len);
            let mut lo = 1u64;
            for bit in 1..=d {
                if (pre >> (bit - 1)) & 1 == 1 {
                    lo |= 1u64 << bit;
                    g = mul_sparse(&g, &facs[bit]);
                }
            }
            let mut out = Vec::new();
            dfs_low(&g, d + 1, lo, k, &facs, classify, &mut out);
            out
        })
        .collect()
}

fn dfs_low<F: Fn(u64, u32, &Ser2) -> u8>(
    g: &Ser2,
    i: usize, // digits < i fixed
    lo: u64,
    k: u32,
    facs: &[Vec<usize>],
    classify: &F,
    out: &mut Vec<(u64, u8)>,
) {
    if i >= k as usize {
        out.push((lo, classify(lo, k, g)));
        return;
    }
    dfs_low(g, i + 1, lo, k, facs, classify, out);
    let h = mul_sparse(g, &facs[i]);
    dfs_low(&h, i + 1, lo | (1u64 << i), k, facs, classify, out);
}

/// Early exit test of Lemma 1: true iff every class mod p has two odd coefficients at indices
/// N >= p^2 that differ mod p^2 (same condition as all(pairs(f, p))).
fn closed_fast(f: &Ser2, p: usize) -> bool {
    let p2 = p * p;
    let mut first = vec![usize::MAX; p];
    let mut done = vec![false; p];
    let mut ndone = 0usize;
    let w0 = p2 >> 6;
    for (wi, &word) in f.w.iter().enumerate().skip(w0) {
        let mut x = word;
        while x != 0 {
            let b = x.trailing_zeros() as usize;
            x &= x - 1;
            let n = (wi << 6) + b;
            if n < p2 || n >= f.len {
                continue;
            }
            let rho = n % p;
            if done[rho] {
                continue;
            }
            let r2 = n % p2;
            if first[rho] == usize::MAX {
                first[rho] = r2;
            } else if first[rho] != r2 {
                done[rho] = true;
                ndone += 1;
                if ndone == p {
                    return true;
                }
            }
        }
    }
    false
}
