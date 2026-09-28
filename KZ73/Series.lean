import KZ73.Statement
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic

/-!
# `f₁` modulo 2 and its binary digit structure

`fbar` is the image of `f₁` in `(ZMod 2)⟦X⟧`. The coefficient of `q^n` in `fbar ^ t` is `c t n`
modulo 2. Over `ZMod 2`, `ψ ^ (2^K) = expand (2^K) ψ` (Frobenius), so `fbar ^ t` is the product
over the binary digits `2^i` of `t` of `fbar(q^(2^i))`, and the coefficients below `q^(2^h)`
depend only on `t mod 2^h` (the paper's Lemma 5).
-/

open PowerSeries

namespace KeithZanello

/-- `f₁` reduced modulo 2. -/
noncomputable def fbar : (ZMod 2)⟦X⟧ := PowerSeries.map (Int.castRingHom (ZMod 2)) f₁

theorem coeff_fbar_pow (t n : ℕ) : coeff n (fbar ^ t) = (c t n : ZMod 2) := by
  simp [fbar, c, ← map_pow, coeff_map]

theorem even_c_iff (t n : ℕ) : Even (c t n) ↔ coeff n (fbar ^ t) = 0 := by
  rw [coeff_fbar_pow, ZMod.intCast_zmod_eq_zero_iff_dvd, even_iff_two_dvd]
  norm_num

theorem zmod2_eq_one_iff_ne_zero (x : ZMod 2) : x = 1 ↔ x ≠ 0 := by
  revert x; decide

theorem not_even_c_iff (t n : ℕ) : ¬ Even (c t n) ↔ coeff n (fbar ^ t) = 1 := by
  rw [even_c_iff, zmod2_eq_one_iff_ne_zero]

open Classical in
/-- The coefficients of `fbar`: `1` at the generalized pentagonal numbers, `0` elsewhere
(Euler's pentagonal number theorem, from Mathlib). -/
theorem coeff_fbar (n : ℕ) :
    coeff n fbar = if n ∈ Set.range pentagonal then 1 else 0 := by
  rw [fbar, coeff_map, f₁_eq_pentagonalSeries]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [coeff_pentagonalSeries_pentagonal]
    rcases Int.even_or_odd k with hk | hk
    · simp [Int.negOnePow_even _ hk]
    · simp [Int.negOnePow_odd _ hk]
  · rw [coeff_pentagonalSeries_eq_zero ℤ h, map_zero]

theorem coeff_zero_fbar : coeff 0 fbar = 1 := by
  have : (0 : ℕ) ∈ Set.range pentagonal := ⟨0, by simp [pentagonal]⟩
  simp [coeff_fbar, this]

theorem coeff_one_fbar : coeff 1 fbar = 1 := by
  have : (1 : ℕ) ∈ Set.range pentagonal := ⟨1, by simp [pentagonal]⟩
  simp [coeff_fbar, this]

/-! ## Frobenius -/

theorem two_pow_ne_zero' (K : ℕ) : 2 ^ K ≠ 0 := pow_ne_zero K two_ne_zero

theorem expand_congr {R : Type*} [CommRing R] {n m : ℕ} (h : n = m) (hn : n ≠ 0) (hm : m ≠ 0)
    (ψ : R⟦X⟧) : expand n hn ψ = expand m hm ψ := by
  subst h; rfl

/-- Over `ZMod 2`, raising to the power `2^K` is the substitution `q ↦ q^(2^K)`. -/
theorem pow_two_pow_eq_expand (ψ : (ZMod 2)⟦X⟧) (K : ℕ) :
    ψ ^ (2 ^ K) = expand (2 ^ K) (two_pow_ne_zero' K) ψ := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h2 : ∀ g : (ZMod 2)⟦X⟧, g ^ 2 = expand 2 two_ne_zero g := by
      intro g
      have := FiniteField.PowerSeries.expand_card g
      simpa [ZMod.card] using this.symm
    calc ψ ^ (2 ^ (K + 1)) = (ψ ^ (2 ^ K)) ^ 2 := by rw [← pow_mul, pow_succ]
      _ = expand 2 two_ne_zero (expand (2 ^ K) (two_pow_ne_zero' K) ψ) := by rw [ih, h2]
      _ = expand (2 * 2 ^ K) (mul_ne_zero two_ne_zero (two_pow_ne_zero' K)) ψ := by
        rw [expand_mul]
      _ = _ := expand_congr (by ring) _ _ _

theorem coeff_pow_two_pow (ψ : (ZMod 2)⟦X⟧) (K n : ℕ) :
    coeff n (ψ ^ (2 ^ K)) = if 2 ^ K ∣ n then coeff (n / 2 ^ K) ψ else 0 := by
  rw [pow_two_pow_eq_expand, coeff_expand]

/-! ## Truncation helpers -/

theorem coeff_mul_of_dvd_sub_one {R : Type*} [CommRing R] (A u : R⟦X⟧) {L N : ℕ}
    (hu : (X : R⟦X⟧) ^ L ∣ u - 1) (hN : N < L) : coeff N (A * u) = coeff N A := by
  obtain ⟨v, hv⟩ := hu
  have : A * u = A + X ^ L * (A * v) := by
    have : u = 1 + X ^ L * v := by rw [← hv]; ring
    rw [this]; ring
  rw [this, map_add, coeff_X_pow_mul', ite_eq_right (by omega), add_zero]

theorem X_pow_dvd_pow_sub_one {R : Type*} [CommRing R] (u : R⟦X⟧) {L : ℕ} (m : ℕ)
    (hu : (X : R⟦X⟧) ^ L ∣ u - 1) : (X : R⟦X⟧) ^ L ∣ u ^ m - 1 := by
  have := sub_dvd_pow_sub_pow u 1 m
  rw [one_pow] at this
  exact dvd_trans hu this

/-- `fbar ^ (2^h) ≡ 1 (mod q^(2^h))`. -/
theorem X_pow_dvd_fbar_pow_two_pow_sub_one (h : ℕ) :
    (X : (ZMod 2)⟦X⟧) ^ (2 ^ h) ∣ fbar ^ (2 ^ h) - 1 := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, coeff_pow_two_pow, coeff_one]
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp [coeff_zero_fbar]
  · have : ¬ 2 ^ h ∣ m := fun hd ↦ absurd (Nat.le_of_dvd hm0 hd) (by omega)
    simp [this, hm0.ne']

/-- **The paper's Lemma 5**: the coefficients of `fbar ^ T` below `q^(2^h)` depend only on
`T mod 2^h`. -/
theorem coeff_fbar_pow_mod (T h N : ℕ) (hN : N < 2 ^ h) :
    coeff N (fbar ^ T) = coeff N (fbar ^ (T % 2 ^ h)) := by
  conv_lhs => rw [← Nat.mod_add_div T (2 ^ h), pow_add, pow_mul]
  exact coeff_mul_of_dvd_sub_one _ _
    (X_pow_dvd_pow_sub_one _ _ (X_pow_dvd_fbar_pow_two_pow_sub_one h)) hN

/-- `fbar ^ (2^K) ≡ 1 + q^(2^K) (mod q^(2^(K+1)))`. -/
theorem X_pow_dvd_fbar_pow_two_pow_sub (K : ℕ) :
    (X : (ZMod 2)⟦X⟧) ^ (2 ^ (K + 1)) ∣ fbar ^ (2 ^ K) - (1 + X ^ (2 ^ K)) := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, map_add, coeff_pow_two_pow, coeff_one, coeff_X_pow]
  have hK : 0 < 2 ^ K := Nat.two_pow_pos K
  rw [pow_succ] at hm
  by_cases hd : 2 ^ K ∣ m
  · obtain ⟨j, rfl⟩ := hd
    have hj : j < 2 := by
      by_contra hj; push Not at hj
      have := Nat.mul_le_mul_left (2 ^ K) hj; omega
    interval_cases j
    · simp [coeff_zero_fbar, hK.ne]
    · simp [coeff_one_fbar]
  · have h1 : m ≠ 0 := fun h ↦ hd (h ▸ dvd_zero _)
    have h2 : m ≠ 2 ^ K := fun h ↦ hd (h ▸ dvd_refl _)
    simp [hd, h1, h2]

/-- **Expansion near a centre** (used in the paper's Lemma 13): for `N < 2^(K+1)`,
`[q^N] fbar^(t + 2^K (2m+1)) = [q^N] fbar^t + [q^(N - 2^K)] fbar^t`. -/
theorem coeff_fbar_pow_centre (t K m N : ℕ) (hN : N < 2 ^ (K + 1)) :
    coeff N (fbar ^ (t + 2 ^ K * (2 * m + 1))) =
      coeff N (fbar ^ t) + if 2 ^ K ≤ N then coeff (N - 2 ^ K) (fbar ^ t) else 0 := by
  have hsplit : fbar ^ (t + 2 ^ K * (2 * m + 1)) =
      fbar ^ t * fbar ^ (2 ^ K) * (fbar ^ (2 ^ (K + 1))) ^ m := by
    rw [← pow_add, ← pow_mul, ← pow_add]; congr 1; ring
  rw [hsplit, coeff_mul_of_dvd_sub_one _ _
    (X_pow_dvd_pow_sub_one _ _ (X_pow_dvd_fbar_pow_two_pow_sub_one (K + 1))) hN]
  obtain ⟨v, hv⟩ := X_pow_dvd_fbar_pow_two_pow_sub K
  have : fbar ^ t * fbar ^ (2 ^ K) =
      fbar ^ t + fbar ^ t * X ^ (2 ^ K) + X ^ (2 ^ (K + 1)) * (fbar ^ t * v) := by
    have : fbar ^ (2 ^ K) = 1 + X ^ (2 ^ K) + X ^ (2 ^ (K + 1)) * v := by
      rw [← hv]; ring
    rw [this]; ring
  rw [this, map_add, map_add, coeff_X_pow_mul', ite_eq_right (by omega), add_zero,
    coeff_mul_X_pow']

/-- **Expansion in a sparse ball** (used in the paper's Lemma 15):
`[q^N] fbar^(τ + 2^K w) = ∑_{a ≤ N, 2^K ∣ N - a} [q^a] fbar^τ · [q^((N-a)/2^K)] fbar^w`. -/
theorem coeff_fbar_pow_sparse (τ K w N : ℕ) :
    coeff N (fbar ^ (τ + 2 ^ K * w)) =
      ∑ a ∈ Finset.range (N + 1), coeff a (fbar ^ τ) *
        (if 2 ^ K ∣ N - a then coeff ((N - a) / 2 ^ K) (fbar ^ w) else 0) := by
  rw [pow_add, mul_comm (2 ^ K) w, pow_mul, pow_two_pow_eq_expand (fbar ^ w), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [coeff_expand]

end KeithZanello
