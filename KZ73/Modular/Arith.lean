import KZ73.Modular.Coeffs
import KZ73.Series
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Defs

/-!
# Arithmetic of the weight 2 Eisenstein series on `Γ₀(9)`

* `σ₁(n)` is divisible by 3 when `n ≡ 2 (mod 3)` (divisor pairing), so `F₂ = M₂ / 3` has integer
  coefficients.
* `σ₁(n)` is odd exactly when the odd part of `n` is a square.
* The integer series `h0z`, `m1z`, `f2z` (orders 0, 1, 2, leading coefficient 1) and
  `wz = h0z · lz + lz²` with `lz = m1z + 3 f2z = ∑_{3 ∤ n} σ₁(n) qⁿ`; modulo 2,
  `wz ≡ q f̄(q²⁴)`, the reduction of `η(24z)`, so the coefficients of `wz ^ t` are `a t m` mod 2.
-/

open PowerSeries Finset
open scoped ArithmeticFunction.sigma

namespace KeithZanello.Modular

/-! ## Divisor sums -/

/-- For `n ≡ 2 (mod 3)`, every divisor pair `d · e = n` has `d + e ≡ 0 (mod 3)`. -/
theorem three_dvd_sigma_one {n : ℕ} (hn : n % 3 = 2) : 3 ∣ σ 1 n := by
  have hsum : 2 * σ 1 n = ∑ d ∈ n.divisors, (d + n / d) := by
    rw [sum_add_distrib, ArithmeticFunction.sigma_one_apply, two_mul]
    congr 1
    exact (Nat.sum_div_divisors n id).symm
  have hdvd : 3 ∣ ∑ d ∈ n.divisors, (d + n / d) := by
    refine dvd_sum fun d hd ↦ ?_
    obtain ⟨hdn, hn0⟩ := Nat.mem_divisors.mp hd
    have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdn
    have key : ∀ x y : ZMod 3, x * y = 2 → x + y = 0 := by decide
    have h2 : ((d : ZMod 3) * ((n / d : ℕ) : ZMod 3)) = 2 := by
      rw [← Nat.cast_mul, hmul]
      have : (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod n 3).symm
      rw [this, hn]; rfl
    have := key _ _ h2
    rw [← Nat.cast_add] at this
    exact (ZMod.natCast_eq_zero_iff _ 3).mp this
  have : 3 ∣ 2 * σ 1 n := hsum ▸ hdvd
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this)

/-- Modulo 2, `σ₁(n)` counts the odd divisors of `n`. -/
theorem sigma_one_zmod_two (n : ℕ) :
    ((σ 1 n : ℕ) : ZMod 2) = ((n.divisors.filter Odd).card : ZMod 2) := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun d _ ↦ ?_
  rcases Nat.even_or_odd d with h | h
  · rw [ite_eq_right (Nat.not_odd_iff_even.mpr h), Nat.cast_zero]
    exact (ZMod.natCast_eq_zero_iff_even).mpr h
  · rw [ite_eq_left h, Nat.cast_one]
    exact (ZMod.natCast_eq_one_iff_odd).mpr h

theorem filter_odd_divisors_two_mul (n : ℕ) :
    (2 * n).divisors.filter Odd = n.divisors.filter Odd := by
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, hn⟩, ho⟩
    refine ⟨⟨?_, by omega⟩, ho⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr ho) hd)
  · rintro ⟨⟨hd, hn⟩, ho⟩
    exact ⟨⟨dvd_mul_of_dvd_right hd 2, by omega⟩, ho⟩

theorem sigma_one_two_mul_zmod_two (n : ℕ) :
    ((σ 1 (2 * n) : ℕ) : ZMod 2) = ((σ 1 n : ℕ) : ZMod 2) := by
  rw [sigma_one_zmod_two, sigma_one_zmod_two, filter_odd_divisors_two_mul]

theorem zmod_two_natCast_succ (e : ℕ) : ((e + 1 : ℕ) : ZMod 2) = if Even e then 1 else 0 := by
  split_ifs with h
  · rw [ZMod.natCast_eq_one_iff_odd]; exact h.add_one
  · rw [ZMod.natCast_eq_zero_iff_even]; exact (Nat.not_even_iff_odd.mp h).add_one

/-- For odd `n`, `σ₁(n)` is odd if and only if `n` is a square. -/
theorem sigma_one_odd_zmod_two {n : ℕ} (hn : Odd n) :
    ((σ 1 n : ℕ) : ZMod 2) = if IsSquare n then 1 else 0 := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hn)
  have hfilt : n.divisors.filter Odd = n.divisors := by
    refine filter_true_of_mem fun d hd ↦ ?_
    exact Odd.of_dvd_nat hn (Nat.dvd_of_mem_divisors hd)
  rw [sigma_one_zmod_two, hfilt, Nat.card_divisors hn0, Nat.cast_prod]
  simp_rw [zmod_two_natCast_succ]
  by_cases hsq : ∀ p : ℕ, p.Prime → Even (n.factorization p)
  · rw [ite_eq_left (Nat.isSquare_iff_even_factorization.mpr hsq)]
    refine prod_eq_one fun p hp ↦ ?_
    rw [ite_eq_left (hsq p (Nat.prime_of_mem_primeFactors hp))]
  · rw [ite_eq_right (fun h ↦ hsq (Nat.isSquare_iff_even_factorization.mp h))]
    push Not at hsq
    obtain ⟨p, hp, hodd⟩ := hsq
    have hmem : p ∈ n.primeFactors := by
      rw [Nat.mem_primeFactors]
      refine ⟨hp, ?_, hn0⟩
      by_contra hnd
      exact hodd (by rw [Nat.factorization_eq_zero_of_not_dvd hnd]; exact ⟨0, rfl⟩)
    exact prod_eq_zero hmem (ite_eq_right hodd)

/-! ## The integer series -/

/-- `H₀ = 1 + 12 ∑ (σ(n) - 3 σ(n/3)) qⁿ`. -/
noncomputable def h0z : ℤ⟦X⟧ := PowerSeries.mk h0Coeff

/-- `M₁ = ∑_{n ≡ 1 (3)} σ(n) qⁿ`. -/
noncomputable def m1z : ℤ⟦X⟧ := PowerSeries.mk m1Coeff

/-- Coefficients of `F₂ = M₂ / 3`. -/
def f2Coeff (n : ℕ) : ℤ := m2Coeff n / 3

/-- `F₂ = (1/3) ∑_{n ≡ 2 (3)} σ(n) qⁿ`, with integer coefficients (`three_dvd_sigma_one`). -/
noncomputable def f2z : ℤ⟦X⟧ := PowerSeries.mk f2Coeff

theorem m2Coeff_eq (n : ℕ) : m2Coeff n = 3 * f2Coeff n := by
  unfold f2Coeff m2Coeff
  split_ifs with h
  · obtain ⟨q, hq⟩ := three_dvd_sigma_one h
    rw [hq]; push_cast; omega
  · rfl

/-- `L = M₁ + M₂ = ∑_{3 ∤ n} σ(n) qⁿ`. -/
noncomputable def lz : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ m1Coeff n + m2Coeff n

/-- `W = H₀ L + L²`, congruent to `η(24z)` modulo 2. -/
noncomputable def wz : ℤ⟦X⟧ := h0z * lz + lz ^ 2

theorem coeff_h0z (n : ℕ) : coeff n h0z = h0Coeff n := coeff_mk _ _
theorem coeff_m1z (n : ℕ) : coeff n m1z = m1Coeff n := coeff_mk _ _
theorem coeff_f2z (n : ℕ) : coeff n f2z = f2Coeff n := coeff_mk _ _
theorem coeff_lz (n : ℕ) : coeff n lz = m1Coeff n + m2Coeff n := coeff_mk _ _

theorem coeff_zero_h0z : coeff 0 h0z = 1 := by simp [coeff_h0z, h0Coeff]
theorem coeff_zero_m1z : coeff 0 m1z = 0 := by simp [coeff_m1z, m1Coeff]
theorem coeff_one_m1z : coeff 1 m1z = 1 := by simp [coeff_m1z, m1Coeff]
theorem coeff_zero_f2z : coeff 0 f2z = 0 := by simp [coeff_f2z, f2Coeff, m2Coeff]
theorem coeff_one_f2z : coeff 1 f2z = 0 := by simp [coeff_f2z, f2Coeff, m2Coeff]

theorem coeff_two_f2z : coeff 2 f2z = 1 := by
  have h2 : σ 1 2 = 3 := by
    rw [ArithmeticFunction.sigma_one_apply]; decide
  simp [coeff_f2z, f2Coeff, m2Coeff, h2]

theorem coeff_zero_lz : coeff 0 lz = 0 := by simp [coeff_lz, m1Coeff, m2Coeff]

theorem coeff_zero_wz : coeff 0 wz = 0 := by
  have hl : constantCoeff lz = 0 := by rw [← coeff_zero_eq_constantCoeff_apply, coeff_zero_lz]
  rw [coeff_zero_eq_constantCoeff_apply, wz, map_add, map_mul, map_pow, hl]
  simp

/-! ## Reduction modulo 2 -/

/-- Reduction of integer series modulo 2. -/
noncomputable abbrev red2 : ℤ⟦X⟧ →+* (ZMod 2)⟦X⟧ := PowerSeries.map (Int.castRingHom (ZMod 2))

theorem red2_h0z : red2 h0z = 1 := by
  ext n
  rw [coeff_map, coeff_h0z, coeff_one]
  unfold h0Coeff
  split_ifs with h h3
  · simp
  all_goals rw [map_mul, show (Int.castRingHom (ZMod 2)) 12 = 0 by decide, zero_mul]

theorem coeff_red2_lz (n : ℕ) :
    coeff n (red2 lz) = if n % 3 = 0 then 0 else ((σ 1 n : ℕ) : ZMod 2) := by
  rw [coeff_map, coeff_lz]
  unfold m1Coeff m2Coeff
  split_ifs <;> first | omega | simp

theorem sq_eq_expand_two (ψ : (ZMod 2)⟦X⟧) : ψ ^ 2 = expand 2 two_ne_zero ψ := by
  have := pow_two_pow_eq_expand ψ 1
  simpa using this

/-- Odd squares prime to 3 are the numbers `24 k + 1` with `k` a generalized pentagonal number. -/
theorem odd_square_iff (n : ℕ) :
    (n % 2 = 1 ∧ n % 3 ≠ 0 ∧ IsSquare n) ↔
      (1 ≤ n ∧ 24 ∣ n - 1 ∧ (n - 1) / 24 ∈ Set.range pentagonal) := by
  constructor
  · rintro ⟨h2, h3, m, rfl⟩
    have hm2 : m % 2 = 1 := by
      rcases Nat.even_or_odd m with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · exfalso; rw [show (r + r) * (r + r) = 2 * (2 * r * r) by ring] at h2; omega
      · omega
    have hm3 : m % 3 ≠ 0 := by
      intro h; apply h3
      obtain ⟨r, rfl⟩ := Nat.dvd_of_mod_eq_zero h
      rw [show 3 * r * (3 * r) = 3 * (3 * r * r) by ring]; omega
    have hm6 : m % 6 = 1 ∨ m % 6 = 5 := by omega
    obtain ⟨k, hk⟩ : ∃ k : ℤ, (m : ℤ) * m = (6 * k - 1) ^ 2 := by
      rcases hm6 with h | h
      · obtain ⟨j, rfl⟩ : ∃ j, m = 6 * j + 1 := ⟨m / 6, by omega⟩
        exact ⟨-(j : ℤ), by push_cast; ring⟩
      · obtain ⟨j, rfl⟩ : ∃ j, m = 6 * j + 5 := ⟨m / 6, by omega⟩
        exact ⟨(j : ℤ) + 1, by push_cast; ring⟩
    have hpent := two_mul_natCast_pentagonal k
    have hm1 : 1 ≤ m * m := Nat.one_le_iff_ne_zero.mpr (by
      intro h; rcases Nat.mul_eq_zero.mp h with h | h <;> omega)
    have key : m * m - 1 = 24 * pentagonal k := by
      zify [hm1]
      linear_combination hk - 12 * hpent
    refine ⟨hm1, ⟨_, key⟩, k, ?_⟩
    rw [key, Nat.mul_div_cancel_left _ (by norm_num)]
  · rintro ⟨h1, hdvd, k, hk⟩
    have hpent := two_mul_natCast_pentagonal k
    have key : n - 1 = 24 * pentagonal k := by
      rw [hk]; exact (Nat.mul_div_cancel' hdvd).symm
    refine ⟨by omega, by omega, (6 * k - 1).natAbs, ?_⟩
    have hn : (n : ℤ) = 24 * pentagonal k + 1 := by zify [h1] at key; linarith
    zify
    rw [abs_mul_abs_self, hn]
    linear_combination 12 * hpent

theorem coeff_X_mul_expand_fbar (n : ℕ) :
    coeff n (X * expand 24 (by norm_num) fbar) =
      if n % 2 = 1 ∧ n % 3 ≠ 0 ∧ IsSquare n then 1 else 0 := by
  classical
  rw [if_congr (odd_square_iff n) rfl rfl]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_expand, coeff_fbar]
    simp only [Nat.add_sub_cancel, le_add_iff_nonneg_left, zero_le, true_and]
    split_ifs <;> tauto

/-- **`W ≡ η(24z) (mod 2)`**: modulo 2, `wz = q f̄(q²⁴)`. -/
theorem red2_wz : red2 wz = X * expand 24 (by norm_num) fbar := by
  classical
  have hw : red2 wz = red2 lz + expand 2 two_ne_zero (red2 lz) := by
    rw [wz, map_add, map_mul, map_pow, red2_h0z, one_mul, sq_eq_expand_two]
  ext n
  rw [hw, map_add, coeff_expand, coeff_X_mul_expand_fbar, coeff_red2_lz]
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hodd
  · -- `n = 2 m`: the two terms cancel, and `2 m` is not an odd square
    have hn : ¬ ((m + m) % 2 = 1 ∧ (m + m) % 3 ≠ 0 ∧ IsSquare (m + m)) := by omega
    have h2 : 2 ∣ m + m := ⟨m, by ring⟩
    rw [ite_eq_right hn, ite_eq_left h2, show (m + m) / 2 = m by omega, coeff_red2_lz]
    by_cases h3 : m % 3 = 0
    · rw [ite_eq_left (show (m + m) % 3 = 0 by omega), ite_eq_left h3, add_zero]
    · rw [ite_eq_right (show ¬ (m + m) % 3 = 0 by omega), ite_eq_right h3,
        show m + m = 2 * m by ring, sigma_one_two_mul_zmod_two]
      exact CharTwo.add_self_eq_zero _
  · have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
    have h2 : ¬ 2 ∣ n := by omega
    rw [ite_eq_right h2, add_zero, sigma_one_odd_zmod_two hodd]
    by_cases h3 : n % 3 = 0
    · rw [ite_eq_left h3]; simp [h3]
    · rw [ite_eq_right h3]; simp [h3, hn2]

/-- Modulo 2, the coefficient of `qᵐ` in `W^t` is that of `η(24z)^t`. -/
theorem coeff_wz_pow_zmod_two (t m : ℕ) : ((coeff m (wz ^ t) : ℤ) : ZMod 2) = (a t m : ZMod 2) := by
  have h : red2 (wz ^ t) = X ^ t * expand 24 (by norm_num) (fbar ^ t) := by
    rw [map_pow, red2_wz, mul_pow, map_pow]
  have := congrArg (coeff m) h
  rw [coeff_map] at this
  rw [show ((coeff m (wz ^ t) : ℤ) : ZMod 2) = Int.castRingHom (ZMod 2) (coeff m (wz ^ t)) from rfl,
    this, coeff_X_pow_mul', a]
  by_cases ht : t ≤ m
  · rw [ite_eq_left ht, coeff_expand]
    by_cases h24 : 24 ∣ m - t
    · rw [ite_eq_left h24, ite_eq_left ⟨ht, h24⟩, coeff_fbar_pow]
    · rw [ite_eq_right h24, ite_eq_right (fun h ↦ h24 h.2), Int.cast_zero]
  · rw [ite_eq_right ht, ite_eq_right (fun h ↦ ht h.1), Int.cast_zero]

end KeithZanello.Modular
