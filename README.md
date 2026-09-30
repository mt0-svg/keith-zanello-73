<h1 align="center">Keith and Zanello's Conjecture B is false</h1>

<p align="center">
  <a href="https://zenodo.org/records/23014001/files/keith-zanello-73.pdf"><img alt="Paper" src="https://img.shields.io/badge/Paper-PDF-b31b1b"></a>
  <a href="https://doi.org/10.5281/zenodo.23014000"><img alt="DOI" src="https://zenodo.org/badge/DOI/10.5281/zenodo.23014000.svg"></a>
  <a href="https://github.com/mt0-svg/keith-zanello-73/actions/workflows/lean_action_ci.yml"><img alt="Lean proof" src="https://github.com/mt0-svg/keith-zanello-73/actions/workflows/lean_action_ci.yml/badge.svg"></a>
  <a href="https://github.com/mt0-svg/keith-zanello-73/actions/workflows/comparator.yml"><img alt="Comparator" src="https://github.com/mt0-svg/keith-zanello-73/actions/workflows/comparator.yml/badge.svg"></a>
  <a href="https://github.com/mt0-svg/keith-zanello-73/actions/workflows/certificates.yml"><img alt="Certificates" src="https://github.com/mt0-svg/keith-zanello-73/actions/workflows/certificates.yml/badge.svg"></a>
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/License-Apache%202.0-blue"></a>
</p>

<p align="center"><i>This is AI-generated research: the results, proofs and code were found and written by AI.<br>Credit goes to all the humans whose work it builds on.</i></p>

## The result

Keith and Zanello conjectured ([Ann. Comb. 2026](https://doi.org/10.1007/s00026-026-00833-x); [arXiv:2404.15716](https://arxiv.org/abs/2404.15716), Conjecture B) that for every prime $`p`$ there are infinitely many odd $`t`$ such that, for some base $`r`$, the coefficients $`c_t(N)`$ of

```math
f_1^t = \prod_{n\ge1} (1-q^n)^t = \sum_{N\ge0} c_t(N)\, q^N
```

are even on the $`p-1`$ progressions $`N = p^2 n + kp + r`$, $`1 \le k \le p-1`$. At $`p = 73`$ exactly twenty odd $`t`$ do, the largest being $`t = 203`$.

```lean
theorem KeithZanello.conjectureB_false : ¬ KeithZanello.ConjectureB
theorem KeithZanello.theorem1 : KeithZanello.Theorem1  -- the twenty t at p = 73
```

## What is checked

- **Lean 4**: both theorems, with Mathlib, no `sorry`, no `native_decide`, only the axioms `propext`, `Classical.choice` and `Quot.sound`. Comparator checks them against the statements of `KZ73/Challenge.lean`. The formal proof of Lemma 11 works on $`\Gamma_0(9)`$ instead of level 576 (paper, paragraph Formalization).
- **Computation**: Theorems 2 and 3 of the paper, at the other primes $`p \equiv 1 \pmod{24}`$ below 2000. For each prime, the Rust program `kztree` writes a certificate, a list of checks that `paper/check.sh` reruns. To guard against a bug in `kztree`, a second program written separately in SageMath and PARI/GP redoes part of this work. At $`p = 73`$ and $`193`$ it recomputes the whole certificate and agrees at every step; at $`p = 97`$ it builds its own certificate, with other parameters, for the same set of exponents $`t`$; at $`p = 337`$ and $`1033`$ it redoes every step except the final search over the residues of $`t`$ modulo powers of 2, which takes most of the running time. At the other 25 primes the certificate was checked by `kztree` alone.

CI runs Comparator and `lake build` at each push, and reruns the computations at each push that touches `code/` or `paper/`, except three checks of the second implementation that take over 10 minutes each (see `code/impl2/README.md`). A tag builds the package from source, runs Comparator on that build and reruns the computations; only if every check passes does it publish the release, with the PDF, the complete output of every CI run and the Lake build archive of the build that Comparator checked.

## Layout

| Path | Content |
|---|---|
| `KZ73/` | the Lean proof (Lean and Mathlib `v4.34.1`); the paper names the Lean counterpart of each numbered statement, or says it is not formalized |
| `KZ73/Challenge.lean`, `KZ73/Solution.lean`, `config.json` | the statements and the Comparator configuration |
| `paper/` | the TeX source, `check.sh` and `small_checks.gp` |
| `code/impl1/` | `kztree` and its recorded certificates at the thirty primes |
| `code/impl2/` | the second implementation, with a README mapping each check to its script and output |
| `code/gp/` | PARI/GP checks: Proposition 4, the level 9 forms of the formalization, the character of $`\eta^8`$, a cross-check of the bad exponents, and a search tool for candidate exponents |

## Check and reuse

Fast check, in a clone at the tag, with the build of the release:

```sh
lake exe cache get          # Mathlib, from its cache
lake build :release         # this package, from the release archive: 3 s
lake build --no-build       # nothing left to build: 4 s
rm -f .lake/build/lib/lean/KZ73/Challenge.* .lake/build/ir/KZ73/Challenge.*
# then Comparator, as .github/workflows/comparator.yml runs it: 4 minutes
```

Comparator trusts the challenge module, which holds the statements: the `rm` line has it compiled again from its source in Comparator's sandbox, and the Lean kernel checks again everything the two theorems use.

Full check, from source: `lake exe cache get && lake build` (the build: 145 s), then Comparator as above.

As a dependency, in a package on Lean `v4.34.1` (`leanprover/lean4:v4.34.1` in `lean-toolchain`) that requires Mathlib at `rev = "v4.34.1"`:

```toml
[[require]]
name = "keith-zanello-73"
git = "https://github.com/mt0-svg/keith-zanello-73"
rev = "v1.2"
```

then `lake update keith-zanello-73`, `lake exe cache get` and `lake build`, which downloads the build archive of the release instead of compiling this package (11 s for a module that imports `KZ73.Solution` and prints the axioms of the two theorems). On a platform other than Linux x86_64, or on another toolchain or Mathlib revision, Lake compiles the package.

These times were measured on a Linux x86_64 workstation limited to 4 cores, with Mathlib's build already on disk and the release archive read from the local disk; a download from GitHub adds its transfer time.

The computations:

```sh
sh paper/check.sh 73 97 193   # three primes; all thirty: about 42 minutes with RAYON_NUM_THREADS=2
sh code/impl2/rerun.sh NAME   # see code/impl2/README.md
```

## Built on

- [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0): the formalization.
- [Comparator](https://github.com/leanprover/comparator) (Apache 2.0): the check of the statements in CI.
- [Fermat's Last Theorem in Lean 4](https://github.com/anthropics/fermats-last-theorem) (the Prove2Me proof repository; Apache 2.0, Copyright 2026 Anthropic, PBC), commit `6e837e75355538c7f80bab5b956861e86c4eacc2`: the Hecke operators and the complex vanishing bound of Sturm on $`\Gamma_0(N)`$, ported to Lean 4.34.1 in `KZ73/Modular/P2M/` (`Sturm`, `HeckeDef`, `HeckeQExp`, `HeckeSlash`, `HeckeCusp`); the construction of $`T_p f`$ in `KZ73/Modular/Hecke.lean` and four lemmas of `KZ73/Modular/EisBasic.lean` follow it. Each of these files names its source files in its header. Changes: the `p2m_*` commands are removed, the declarations move to the namespace `KeithZanello.Modular.P2M`, unused lemmas are omitted and deprecated names replaced; each header lists its own changes.
- [PARI/GP](https://pari.math.u-bordeaux.fr/) and [SageMath](https://github.com/sagemath/sage), with FLINT and NTL: the second implementation and the small checks.

## Citation

```bibtex
@misc{keith-zanello-73,
  title     = {Conjecture {B} of {K}eith and {Z}anello on the parity of eta-powers is false},
  author    = {{mt0-svg}},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23014000},
  url       = {https://doi.org/10.5281/zenodo.23014000}
}
```

## Contact

Questions and corrections: [open an issue](https://github.com/mt0-svg/keith-zanello-73/issues/new/choose).

## License

Apache 2.0 (`LICENSE`, `NOTICE`).
