import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Challenge: Conjecture B of Keith and Zanello is false

The statement to check. Source: W. J. Keith and F. Zanello, *Parity of the coefficients of
certain eta-quotients, III: two special classes*, arXiv:2404.15716v3 (Annals of Combinatorics
2026), Definition 17 and Conjecture B.

* `f₁ = ∏_{n ≥ 1} (1 - q^n)` in `ℤ⟦q⟧`, and `f₁^t = ∑ c_t(n) q^n`.
* Definition 17: `f₁^t` is `(p, r)`-even, for a base `r ∈ {0, …, p^2 - 1}`, if
  `c_t(p^2 n + k p + r)` is even for all `n ≥ 0` and all `k ∈ {1, …, p - 1}`.
* Conjecture B: for every prime `p` there are infinitely many odd `t ≥ 1` such that `f₁^t` is
  `(p, r)`-even for some base `r` (depending on `t` and `p`).

`conjectureB_false` says the conjecture is false. `theorem1` is the precise result at `p = 73`:
the odd `t` for which `f₁^t` is `73^2`-even are exactly the twenty elements of `E73`, with the
base `222 t mod 73^2`, unique for `t ≥ 5`.

The definitions are copied from `KZ73/Statement.lean`; `KZ73/Solution.lean` imports the proofs, and
Comparator (`config.json`) checks that they prove these two statements with the standard axioms.
-/

open PowerSeries PowerSeries.WithPiTopology

namespace KeithZanello

/-- Euler's product `f₁ = ∏_{n ≥ 1} (1 - q^n)` in `ℤ⟦q⟧`, as the infinite product
`∏' n : ℕ, (1 - X^(n+1))` for the coefficientwise topology on `ℤ⟦X⟧` (`ℤ` discrete).
The product converges (`f₁_hasProd` below), and `c_eq_coeff_finite_prod` shows that
`c t n` is the coefficient of `q^n` in the `t`-th power of the finite product
`∏_{k=1}^{n} (1 - q^k)`. -/
noncomputable def f₁ : ℤ⟦X⟧ := ∏' n : ℕ, (1 - X ^ (n + 1))

/-- `c t n` is the coefficient of `q^n` in `f₁^t = ∏_{n ≥ 1} (1 - q^n)^t`. -/
noncomputable def c (t n : ℕ) : ℤ := coeff n (f₁ ^ t)

/-- Keith and Zanello, Definition 17: `f₁^t` is `(p, r)`-even when `c_t(p^2 n + k p + r)` is even
for all `n ≥ 0` and all `k ∈ {1, …, p - 1}`. The base `r` is required to lie in
`{0, …, p^2 - 1}` where the definition is used (`IsP2Even`). -/
def IsEvenWithBase (p t r : ℕ) : Prop :=
  ∀ n k : ℕ, 1 ≤ k → k ≤ p - 1 → Even (c t (p ^ 2 * n + k * p + r))

/-- `f₁^t` is `p^2`-even: it is `(p, r)`-even for some base `r ∈ {0, …, p^2 - 1}`. -/
def IsP2Even (p t : ℕ) : Prop :=
  ∃ r < p ^ 2, IsEvenWithBase p t r

/-- **Conjecture B** of Keith and Zanello: for any prime `p` there exist infinitely many odd
`t ≥ 1` such that `f₁^t` is `(p, r)`-even for some base `r` depending on `t` and `p`.
(For natural numbers, `Odd t` already forces `t ≥ 1`.) -/
def ConjectureB : Prop :=
  ∀ p : ℕ, p.Prime → {t : ℕ | Odd t ∧ IsP2Even p t}.Infinite

/-- The set `𝓔₇₃` of the paper's Theorem 1. -/
def E73 : Finset ℕ :=
  {1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 51, 55, 59, 61, 65, 69, 199, 203}

/-- The paper's Theorem 1: for odd `t`, `f₁^t` is `73^2`-even if and only if `t ∈ E73`; for each
`t ∈ E73`, `f₁^t` is `(73, r_t)`-even with `r_t = 222 t mod 73^2`; and for `t ≥ 5` in `E73` this
is the only base. -/
def Theorem1 : Prop :=
  {t : ℕ | Odd t ∧ IsP2Even 73 t} = (E73 : Set ℕ) ∧
  (∀ t ∈ E73, IsEvenWithBase 73 t (222 * t % 73 ^ 2)) ∧
  (∀ t ∈ E73, 5 ≤ t → ∀ r < 73 ^ 2, IsEvenWithBase 73 t r → r = 222 * t % 73 ^ 2)

/-- Keith and Zanello's Conjecture B is false. -/
theorem conjectureB_false : ¬ ConjectureB := sorry

/-- Theorem 1 of the paper: the odd `t` with `f₁^t` `73^2`-even, their bases, and uniqueness. -/
theorem theorem1 : Theorem1 := sorry

end KeithZanello
