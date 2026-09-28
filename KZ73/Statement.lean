import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Keith and Zanello's Conjecture B: definitions

Everything a reader must check against the literature is in this file.

Source: W. J. Keith and F. Zanello, *Parity of the coefficients of certain eta-quotients, III:
two special classes*, arXiv:2404.15716v3 (Annals of Combinatorics 2026), Definition 17 and
Conjecture B, quoted in the paper `paper/main.tex` of this problem folder (Section 1).

* `f₁ = ∏_{n ≥ 1} (1 - q^n)`, an infinite product in `ℤ⟦q⟧`, and `f₁^t = ∑ c_t(n) q^n`.
* Definition 17: `f₁^t` is `(p, r)`-even, for a base `r ∈ {0, …, p^2 - 1}`, if
  `c_t(p^2 n + k p + r)` is even for all `n ≥ 0` and all `k ∈ {1, …, p - 1}`.
* `f₁^t` is `p^2`-even if it is `(p, r)`-even for some base `r`.
* Conjecture B: for every prime `p` there are infinitely many odd `t ≥ 1` such that `f₁^t` is
  `(p, r)`-even for some base `r` (depending on `t` and `p`).

`Theorem1` below says that at `p = 73` the odd `t` for which `f₁^t` is `73^2`-even are exactly
the twenty elements of `E73`, the largest being `203`; `not_conjectureB_of_theorem1` derives
`¬ ConjectureB` from it. `KZ73/Main.lean` proves `MainClaim` (Theorem 1 assuming
`SturmHypothesis`, the paper's Lemma 11) and `MainClaimG` (Theorem 1 assuming condition (G) for
the eighteen elements `t ≥ 5` of `E73`). `KZ73/Modular/Final.lean` proves `SturmHypothesis`
(`sturmHypothesis_proved`, through modular forms of level 9), hence `theorem1 : Theorem1` and
`conjectureB_false : ¬ ConjectureB` with no hypothesis.
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

/-! ## The modular step (the paper's Lemma 11)

`a t m` is the coefficient of `q^m` in `η(24z)^t = q^t f₁(q^24)^t = ∑_n c_t(n) q^(24n+t)`. For a
prime `p ≥ 5`, `heckeCoeff p t m = a t (p m) + a t (m / p)` (the second term only when `p ∣ m`)
is, modulo 2, the coefficient of `q^m` in `T_p H_t`, where
`H_t = η(z)^2 η(24z)^t / η(2z) ≡ η(24z)^t (mod 2)` is a holomorphic modular form of weight
`(t+1)/2` on `Γ₀(576)` with a quadratic character and `T_p` is the Hecke operator (paper,
proof of Lemma 11). Sturm's theorem then says that `T_p H_t ≡ 0 (mod 2)` as soon as its
coefficients vanish mod 2 up to `(t+1)/2 · [SL₂(ℤ) : Γ₀(576)] / 12 = 48 (t + 1)`. The Lean proof
in `KZ73/Modular/` takes a level 9 route instead (see `KZ73/Modular/Final.lean`). -/

/-- `a t m`: the coefficient of `q^m` in `η(24z)^t = ∑_n c_t(n) q^(24 n + t)`. -/
noncomputable def a (t m : ℕ) : ℤ :=
  if t ≤ m ∧ 24 ∣ m - t then c t ((m - t) / 24) else 0

/-- `a t (p m) + a t (m / p)`, the second term only when `p ∣ m`; modulo 2 this is the
coefficient of `q^m` in `T_p H_t`, where `H_t ≡ η(24z)^t (mod 2)` is the integral weight form of
Lemma 11 (for odd `t`, `η(24z)^t` itself has half-integral weight). -/
noncomputable def heckeCoeff (p t m : ℕ) : ℤ :=
  a t (p * m) + if p ∣ m then a t (m / p) else 0

/-- **The paper's Lemma 11** (Sturm's bound for `T_p H_t` modulo 2):
for every prime `p ≥ 5` and every odd `t`, if `heckeCoeff p t m` is even for
`1 ≤ m ≤ 48 (t + 1)` then it is even for every `m ≥ 1`.

The paper derives it from the theorems of Gordon and Hughes and of Newman (modularity of the eta
quotient `H_t`), Ligozat (holomorphy at the cusps), the action of Hecke operators on
`M_k(Γ₀(N), χ)`, and Sturm's congruence theorem. `KZ73/Main.lean` takes it as an argument;
`KZ73/Modular/Final.lean` proves it (`sturmHypothesis_proved`) with forms on `Γ₀(9)` and the
sharper bound `4 t`. -/
def SturmHypothesis : Prop :=
  ∀ p t : ℕ, p.Prime → 5 ≤ p → Odd t →
    (∀ m, 1 ≤ m → m ≤ 48 * (t + 1) → Even (heckeCoeff p t m)) →
    ∀ m, 1 ≤ m → Even (heckeCoeff p t m)

/-- The instance of `SturmHypothesis` that is used: `p = 73` and the eighteen elements `t ≥ 5`
of `E73`. It follows from `SturmHypothesis` (`sturmHypothesis73_of_sturmHypothesis`). -/
def SturmHypothesis73 : Prop :=
  ∀ t ∈ E73, 5 ≤ t →
    (∀ m, 1 ≤ m → m ≤ 48 * (t + 1) → Even (heckeCoeff 73 t m)) →
    ∀ m, 1 ≤ m → Even (heckeCoeff 73 t m)

/-- The conclusion of the paper's Lemma 11 at `p = 73` for the eighteen elements `t ≥ 5` of
`E73`: `T_73 H_t ≡ 0 (mod 2)`, stated on `q`-expansion coefficients. -/
def Hecke73 : Prop := ∀ t ∈ E73, 5 ≤ t → ∀ m, 1 ≤ m → Even (heckeCoeff 73 t m)


/-! ## The statements proved in `KZ73/Main.lean` and `KZ73/Modular/Final.lean`

`r_t` is the residue of `-t / 24` modulo `73^2`; since `24 * 222 = 73^2 - 1`, it is `222 t mod 5329`. -/

/-- The paper's Theorem 1: for odd `t`, `f₁^t` is `73^2`-even if and only if `t ∈ E73`; for each
`t ∈ E73`, `f₁^t` is `(73, r_t)`-even with `r_t = 222 t mod 73^2`; and for `t ≥ 5` in `E73` this
is the only base. -/
def Theorem1 : Prop :=
  {t : ℕ | Odd t ∧ IsP2Even 73 t} = (E73 : Set ℕ) ∧
  (∀ t ∈ E73, IsEvenWithBase 73 t (222 * t % 73 ^ 2)) ∧
  (∀ t ∈ E73, 5 ≤ t → ∀ r < 73 ^ 2, IsEvenWithBase 73 t r → r = 222 * t % 73 ^ 2)

/-- Condition (G) of the paper (Lemma 13): `c_t(N)` is even whenever `p` divides `24 N + t`
exactly once. -/
def CondG (p t : ℕ) : Prop :=
  ∀ N : ℕ, p ∣ 24 * N + t → ¬ p ^ 2 ∣ 24 * N + t → Even (c t N)

/-- The main result, proved in `KZ73/Main.lean`: the paper's Lemma 11 implies Theorem 1. -/
def MainClaim : Prop := SturmHypothesis → Theorem1

/-- Variant proved in `KZ73/Main.lean`: condition (G) at `p = 73` for the eighteen elements
`t ≥ 5` of `E73` implies Theorem 1. -/
def MainClaimG : Prop := (∀ t ∈ E73, 5 ≤ t → CondG 73 t) → Theorem1

/-- Theorem 1 disproves Conjecture B (at `p = 73`). -/
theorem not_conjectureB_of_theorem1 (h : Theorem1) : ¬ ConjectureB := by
  intro hB
  have hinf := hB 73 (by decide)
  rw [h.1] at hinf
  exact hinf (E73 : Finset ℕ).finite_toSet

/-! ## Sanity lemmas for the definition of `f₁` and `c` -/

theorem f₁_eq_pentagonalSeries : f₁ = pentagonalSeries ℤ :=
  tprod_one_sub_X_pow ℤ

/-- The infinite product defining `f₁` converges to `f₁`. -/
theorem f₁_hasProd : HasProd (fun n : ℕ ↦ (1 - X ^ (n + 1) : ℤ⟦X⟧)) f₁ := by
  rw [f₁_eq_pentagonalSeries]; exact hasProd_one_sub_X_pow ℤ

private theorem X_pow_dvd_prod_sub_one (n : ℕ) (s : Finset ℕ) (hs : ∀ k ∈ s, n ≤ k) :
    (X : ℤ⟦X⟧) ^ (n + 1) ∣ (∏ k ∈ s, (1 - X ^ (k + 1) : ℤ⟦X⟧)) - 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    have h1 : (X : ℤ⟦X⟧) ^ (n + 1) ∣ (1 - X ^ (j + 1) : ℤ⟦X⟧) - 1 := by
      have : n + 1 ≤ j + 1 := by have := hs j (Finset.mem_insert_self j s); omega
      simpa using (pow_dvd_pow (X : ℤ⟦X⟧) this).neg_right
    have h2 := ih (fun k hk ↦ hs k (Finset.mem_insert_of_mem hk))
    have : (1 - X ^ (j + 1) : ℤ⟦X⟧) * ∏ k ∈ s, (1 - X ^ (k + 1)) - 1 =
        (1 - X ^ (j + 1)) * ((∏ k ∈ s, (1 - X ^ (k + 1))) - 1) + ((1 - X ^ (j + 1)) - 1) := by
      ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right h2 _) h1

/-- `f₁ ≡ ∏_{k=1}^{n} (1 - q^k) (mod q^(n+1))`. -/
theorem X_pow_dvd_f₁_sub_finite_prod (n : ℕ) :
    (X : ℤ⟦X⟧) ^ (n + 1) ∣ f₁ - ∏ k ∈ Finset.range n, (1 - X ^ (k + 1)) := by
  rw [X_pow_dvd_iff]
  intro m hm
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.mp
    (coeff_prod_one_sub_X_pow_eventually_eq ℤ m)
  set s := s₀ ∪ Finset.range n
  have hs := hs₀ s Finset.subset_union_left
  rw [map_sub, f₁_eq_pentagonalSeries, ← hs, sub_eq_zero]
  have hsplit : s = Finset.range n ∪ (s \ Finset.range n) := by
    simp [s]
  rw [hsplit, Finset.prod_union Finset.disjoint_sdiff]
  obtain ⟨u, hu⟩ := X_pow_dvd_prod_sub_one n (s \ Finset.range n)
    (fun k hk ↦ by simp at hk; omega)
  rw [sub_eq_iff_eq_add] at hu
  rw [hu, mul_add, mul_one, map_add, add_eq_right, mul_left_comm, coeff_X_pow_mul']
  split_ifs with h
  · omega
  · rfl

/-- `c t n` is the coefficient of `q^n` in `(∏_{k=1}^{n} (1 - q^k))^t`. -/
theorem c_eq_coeff_finite_prod (t n : ℕ) :
    c t n = coeff n ((∏ k ∈ Finset.range n, (1 - X ^ (k + 1) : ℤ⟦X⟧)) ^ t) := by
  have h := dvd_trans (X_pow_dvd_f₁_sub_finite_prod n) (sub_dvd_pow_sub_pow _ _ t)
  rw [X_pow_dvd_iff] at h
  have := h n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at this
  exact this

end KeithZanello
