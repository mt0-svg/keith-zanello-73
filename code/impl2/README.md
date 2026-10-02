# Second implementation

The certificates of the paper are computed by `kztree` (Rust, `code/impl1/`). This directory holds a second implementation, in SageMath and PARI/GP, that tests it: it recomputes the steps of the certificate with other code and other algorithms, and compares its results with the recorded outputs of `kztree` in `code/impl1/out/`.

It was written without reading or translating `kztree.rs` or its series library `ser2.rs`. The differences are these.

| | `kztree` (impl1) | this directory (impl2) |
|---|---|---|
| language | Rust | SageMath 10.9 (`.sage`) and PARI/GP (`.gp`) |
| series modulo 2 | bit arrays (`ser2.rs`) | `GF(2)[x]` of Sage (NTL `GF2X`); FLINT `nmod_poly` and PARI series over `Z/2Z` as further engines |
| `f_1^t` modulo 2 | product of lacunary factors, one per binary digit of `t` or pair of adjacent digits (Lemma 5) | plain truncated powering `P^t` of the pentagonal series `P` (`power_trunc`); no binary digit factorisation |
| sparse balls around 1 and 3 | reduced test of Remark 16(2) | the same test (`certificate_p73.sage`), and the full condition (S) modulo `p²` (`sparse_p73.gp`, `sparse_p97.gp`) |

The engine is validated in `engine_check.sage`: the pentagonal series against the product `∏(1 - q^n)` expanded over `Z` by FLINT, `f_1^t` modulo 2 against the integer power of PARI's `eta` series for 45 values of `t ≤ 257`, and plain powering against the binary digit products for nine values of `t` up to `2^14 + 3`.

Two inputs are shared with `kztree`: the list `E` of each prime and the starting level `kstart`, which `sturm.sage` and `certificate.sage` read from the first line of `code/impl1/out/tree_p<p>.txt`. The certificate proves that the list is complete, so it does not rely on how the list was found.

The comments in the scripts use the numbering of the paper. The printed lines keep an older one: "Lemma 2" and "lemma2" stand for Lemma 13 (a centre), and "sparse" for the balls of Lemma 15.

## What each claim rests on

Every script runs from this directory. The times are wall clock on an AMD Ryzen 9 5900X, measured under a cap of 4 cores and 8 GB with three checks running at once; the times printed inside some recorded outputs come from the original runs on the same machine.

### p = 73: every step of the certificate

| claim | script | recorded output | time |
|---|---|---|---|
| condition (G) (Lemma 11) for the 18 listed `t ≥ 5`, up to four times the Sturm bound; the test fails below the bound for every odd `t < 240` outside `E_73`; level and character of `η(24z)^t θ(z)` from PARI's `mf` package | `sturm_p73.sage` | `sturm_p73.out` | 2 s |
| `K_0 = 13`, `K_0' = 11` (Remark 16(1), `κ = 146`, `μ = 3000`), the test of Remark 16(2), and the search from `h_0 = 14`, with the counts and centres of `code/impl1/out/tree_p73.txt` at every level | `certificate_p73.sage` | `certificate_p73.out` | 151 s |
| condition (S) modulo `73²` with `μ = 300` (`K_0 = 10`, `K_0' = 9`) for the 657 elements of `⟨2⟩` and the 256 odd `w < 2^9`; with `S_τ = {0}` the test fails | `sparse_p73.gp` | `sparse_p73.out` | 35 s |
| the search from `h_0 = 3` with `μ = 300`, with the counts and centres of an earlier `kztree` run, `code/impl1/out/tree_p73_h3.txt` | `search_p73_h3.sage` | `search_p73_h3.out` | 38 s |

The current `kztree` gives the same counts at every level as `tree_p73_h3.txt` when run as `kztree 73 3 18 146 300 <list>`; its output format has changed since that run, so `paper/check.sh` does not compare that file.

### p = 97: a second certificate, with other parameters

| claim | script | recorded output | time |
|---|---|---|---|
| condition (G) for the 27 listed `t ≥ 5`; the test fails for every odd `t < 400` outside the list | `sturm_p97.sage` | `sturm_p97.out` | 2 s |
| condition (S) modulo `97²` with `κ = 194`, `μ = 300` (`K_0 = 11`, `K_0' = 9`) for the 4656 elements of `⟨2⟩` and the 256 odd `w < 2^9` | `sparse_p97.gp` | `sparse_p97.out` | 371 s |
| the search from `h_0 = 15` with these `K_0`, `K_0'`: it ends at level 19 with the 27 centres (`kztree` started at level 14 with `μ = 3000`) | `search_p97.sage` | `search_p97.out` | 451 s |

### p = 193: every step of the certificate

| claim | script | recorded output | time |
|---|---|---|---|
| condition (G) for every listed `t ≥ 5` up to twice the Sturm bound; the test fails for every unlisted odd `t < 250` | `sturm.sage 193 250` | `sturm_p193.out` | 2 s |
| `K_0`, `K_0'` and `M_min` of `code/impl1/out/tree_p193.txt`, the test of Remark 16(2) with `μ = 3000`, and the search from `h_0 = 16` with the same counts and centres at every level | `certificate.sage 193 tree` | `certificate_p193.out` | 708 s |

### p = 337 and p = 1033: every step but the search

| claim | script | recorded output | time |
|---|---|---|---|
| condition (G) up to twice the Sturm bound; the test fails for every unlisted odd `t < 600` | `sturm.sage 337 600` | `sturm_p337.out` | 7 s |
| the same, unlisted odd `t < 2100` | `sturm.sage 1033 2100` | `sturm_p1033.out` | 765 s |
| `K_0`, `K_0'` and `M_min` of `tree_p337.txt`, and the test of Remark 16(2) | `certificate.sage 337` | `certificate_p337.out` | 32 s |
| the same for `tree_p1033.txt` | `certificate.sage 1033` | `certificate_p1033.out` | 1086 s |

The search is not repeated at these two primes, and nothing here is run at the other 25 primes of Table 2.

`certificate.sage` is the code of `certificate_p73.sage` with the prime as an argument, `κ = 2p`, the list and `kstart` read from `code/impl1/out/tree_p<p>.txt`, and the per-node work of the search split between two worker processes. `certificate_run.sh` is the command file of these three runs.

### Further checks at p = 73, outside the certificate

| check | script | recorded output | time |
|---|---|---|---|
| the engine (see above) | `engine_check.sage` | `engine_check.out` | 3 s |
| Theorem 1 for odd `t < 2^16` with no lemma: a pair in every class modulo 73 among the coefficients of `f_1^t` below `2^17`, except for the listed `t` and 8 values `τ + 2^K w` | `brute_p73.sage 16` | `brute_p73.out` | 147 s |
| the same for odd `t` in `[2^16, 2^18)`, below `2^19`: 6 values `τ + 2^K w` are left | `brute_p73_range.sage 65536 163840 19`, `brute_p73_range.sage 163840 262144 19` | `brute_p73_range_a.out`, `brute_p73_range_b.out` | 229 s, 221 s |
| the 8 values below `2^16` and four above `2^18` (`1 + 2^20`, `1 + 2^22`, `3 + 2^20`, `3 + 2^21`) settled by counting the representations `N = P_i + 2^K M` (or `Q_i + 2^K M`), each index recounted by a square test; the conclusion of Lemma 15 checked directly at 657 consecutive `K` and further `K` up to 3000 | `sparse_direct_p73.gp` | `sparse_direct_p73.out` | 16 s |
| the 6 values in `[2^16, 2^18)` settled in the same way | `leftovers_p73.gp` | `leftovers_p73.out` | 1 s |
| explicit pairs for 39 unlisted `t`, rechecked with FLINT (all 39) and by counting representations (23 of them); evenness of the listed `t` on their base below `2 · 10^7` | `spot_p73.sage` | `spot_p73.out` | 322 s |
| the definition read literally on sample `t`, Lemma 14 on sample `T`, the identity behind Lemma 13 | `lemma_sanity_p73.sage` | `lemma_sanity_p73.out` | 14 s |

Three of these outputs end on a `FAIL` line, and none of them is a failure of a claim.

- `brute_p73.out` ends with `ALL-T CHECK: FAIL (differs from the list)`: the script expects the values without a pair below `2^17` to be exactly the listed ones, and 8 values of the form `τ + 2^K w` have their pairs further out. `sparse_direct_p73.out` finds them.
- `spot_p73.out` ends with `SPOT CHECKS: FAIL` for the same reason: `1 + 2^20`, `1 + 2^22`, `3 + 2^20` and `3 + 2^21` have no pair below `2^24`. `sparse_direct_p73.out` finds them.
- `lemma_sanity_p73.out` ends with `LEMMA SANITY: FAIL` because part (A) expects a single surviving base for every listed `t`, and for `t = 1` and `t = 3` many bases survive on the finite range `N < 400000`. Every other line of the file passes.

Together, `brute_p73`, `brute_p73_range`, `sparse_direct_p73` and `leftovers_p73` show that every odd `t < 2^18` outside `E_73` has a pair in every class modulo 73; the 14 values `τ + 2^K w` with `τ, w ∈ {1, 3}` and `13 ≤ K ≤ 17` need indices near `26 · 2^K` (if `w = 1`) or `10 · 2^K` (if `w = 3`).

## Rerunning

```sh
sh code/impl2/rerun.sh engine_check sturm_p73 certificate_p73
```

reruns the named checks and compares each output with the recorded one, ignoring running times, PARI's stack size warnings and trailing blanks; it exits with status 0 when all are identical. The names are the base names of the recorded outputs, and `rerun.sh` holds the command line of each. By hand, from `code/impl2/`: `sage <script>.sage [arguments]` for the Sage scripts, and for the PARI/GP scripts

```sh
gp -q sparse_p73.gp < /dev/null
gp -q -D parisizemax=2000000000 -D nbthreads=1 sparse_p97.gp
gp -q -D parisizemax=3000000000 -D nbthreads=1 sparse_direct_p73.gp
gp -q -D parisizemax=2500000000 -D nbthreads=1 leftovers_p73.gp
```

The recorded outputs come from SageMath 10.9 (with its PARI 2.17.3) and PARI/GP 2.17.4. The same outputs are obtained in the container `sagemath/sagemath:10.9` (PARI 2.17.1 inside Sage) with the `pari-gp` package of Ubuntu 24.04 (PARI/GP 2.15.4). The largest resident memory measured is 0.9 GB (`spot_p73`).

## Continuous integration

The job `impl2` of `.github/workflows/ci.yml` runs `rerun.sh` in the container `sagemath/sagemath:10.9` on every check above except three, which take more than 10 minutes here and so may exceed 20 minutes on a 4-core GitHub runner:

| left out | time here |
|---|---|
| `sturm_p1033` | 765 s |
| `certificate_p193` | 708 s |
| `certificate_p1033` | 1086 s |

Run them locally with `sh code/impl2/rerun.sh sturm_p1033 certificate_p193 certificate_p1033`.

Each job uploads the complete output of its checks as an artifact; for a tagged release, `release.yml` puts them in `verification-<tag>.tar.gz` and indexes them in `VERIFICATION.md`.
