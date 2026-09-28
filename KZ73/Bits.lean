import KZ73.Series
import Mathlib.Data.Nat.Bitwise

/-!
# Truncated `F_2` power series as bits of a natural number

`Rep B L ψ` says that the binary digits of `B` are the coefficients of `ψ ∈ (ZMod 2)⟦X⟧` below
`X^L`, and that `B < 2^L`. The kernel evaluates `Nat` shifts, `xor`, `and`, `or` with GMP, so
the computations below are checked by `decide +kernel` without `native_decide`.

`mulPent B s L` multiplies by `fbar(q^s) = fbar ^ s` (for `s` a power of two) modulo `X^L`: by
Euler's theorem `fbar = ∑_j q^(P_j)`, it is the `xor` of the shifts of `B` by `s P_j < L`.
-/

open PowerSeries

namespace KeithZanello

/-- `2^L - 1`. -/
def mask (L : ℕ) : ℕ := 2 ^ L - 1

theorem testBit_mask (L n : ℕ) : (mask L).testBit n = decide (n < L) :=
  Nat.testBit_two_pow_sub_one L n

/-- `B` represents `ψ` modulo `X^L`. -/
def Rep (B L : ℕ) (ψ : (ZMod 2)⟦X⟧) : Prop :=
  ∀ n, B.testBit n = (decide (n < L) && decide (coeff n ψ = 1))

/-- A boolean as an element of `ZMod 2`. -/
def b2z (x : Bool) : ZMod 2 := if x then 1 else 0

@[simp] theorem b2z_true : b2z true = 1 := rfl
@[simp] theorem b2z_false : b2z false = 0 := rfl

theorem b2z_xor (x y : Bool) : b2z (x ^^ y) = b2z x + b2z y := by
  cases x <;> cases y <;> decide

theorem b2z_and (x y : Bool) : b2z (x && y) = b2z x * b2z y := by
  cases x <;> cases y <;> decide

theorem b2z_decide_eq_one (x : ZMod 2) : b2z (decide (x = 1)) = x := by
  revert x; decide

theorem b2z_decide (P : Prop) [Decidable P] : b2z (decide P) = if P then 1 else 0 := by
  by_cases h : P <;> simp [h, b2z]

/-! ## Shifts and xor -/

/-- `xor` of `acc` with the shifts of `B` by the elements of `ds`, truncated below `2^L`. -/
def xorShifts (B L : ℕ) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | d :: ds, acc => xorShifts B L ds (acc ^^^ ((B <<< d) &&& mask L))

theorem b2z_testBit_xorShifts (B L n : ℕ) (ds : List ℕ) (acc : ℕ) :
    b2z ((xorShifts B L ds acc).testBit n) =
      b2z (acc.testBit n) +
        (ds.map fun d ↦ b2z (decide (d ≤ n) && B.testBit (n - d) && decide (n < L))).sum := by
  induction ds generalizing acc with
  | nil => simp [xorShifts]
  | cons d ds ih =>
    rw [xorShifts, ih, Nat.testBit_xor, b2z_xor, Nat.testBit_land, Nat.testBit_shiftLeft,
      testBit_mask, List.map_cons, List.sum_cons]
    simp only [ge_iff_le]
    ring

/-! ## Pentagonal shifts -/

/-- `P k = k (3k - 1)/2` and `P (-k) = k (3k + 1)/2` for natural `k`. -/
theorem pentagonal_natCast (k : ℕ) : pentagonal (k : ℤ) = k * (3 * k - 1) / 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [pentagonal]
  have h := two_mul_natCast_pentagonal (k : ℤ)
  have h1 : 2 * pentagonal (k : ℤ) = k * (3 * k - 1) := by
    have : ((k * (3 * k - 1) : ℕ) : ℤ) = (k : ℤ) * (3 * k - 1) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ 3 * k)]; ring
    exact_mod_cast h.trans this.symm
  omega

theorem pentagonal_neg_natCast (k : ℕ) : pentagonal (-(k : ℤ)) = k * (3 * k + 1) / 2 := by
  have h := two_mul_natCast_pentagonal_neg (k : ℤ)
  have h1 : 2 * pentagonal (-(k : ℤ)) = k * (3 * k + 1) := by exact_mod_cast h
  omega

/-- The shifts `s P_k, s P_(-k)` for `k ≥ k₀`, in increasing order, as long as they are `< L`. -/
def pentShifts (s L : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, k =>
    if s * (k * (3 * k - 1) / 2) < L then
      if s * (k * (3 * k + 1) / 2) < L then
        s * (k * (3 * k - 1) / 2) :: s * (k * (3 * k + 1) / 2) :: pentShifts s L fuel (k + 1)
      else [s * (k * (3 * k - 1) / 2)]
    else []

theorem pent_lt_pent_neg (k : ℕ) (hk : 1 ≤ k) : k * (3 * k - 1) / 2 < k * (3 * k + 1) / 2 := by
  have := pentagonal_lt_pentagonal_neg (k := (k : ℤ)) (by omega)
  rwa [pentagonal_natCast, pentagonal_neg_natCast] at this

theorem pent_le_pent_neg (k : ℕ) : k * (3 * k - 1) / 2 ≤ k * (3 * k + 1) / 2 :=
  Nat.div_le_div_right (Nat.mul_le_mul_left k (by omega))

theorem pent_neg_lt_pent_succ (k : ℕ) :
    k * (3 * k + 1) / 2 < (k + 1) * (3 * (k + 1) - 1) / 2 := by
  have := pentagonal_neg_lt_pentagonal_add_one (k := (k : ℤ)) (by omega)
  rwa [pentagonal_neg_natCast, show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
    pentagonal_natCast] at this

theorem pent_mono {j k : ℕ} (h : j ≤ k) : j * (3 * j - 1) / 2 ≤ k * (3 * k - 1) / 2 := by
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul h
  omega

theorem le_pent (k : ℕ) : k ≤ k * (3 * k - 1) / 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have : k * 2 ≤ k * (3 * k - 1) := Nat.mul_le_mul_left k (by omega)
  omega

/-- Lower bound: every element of `pentShifts s L fuel k` is at least `s P_k`. -/
theorem pentShifts_ge (s L fuel k d : ℕ) (hd : d ∈ pentShifts s L fuel k) :
    s * (k * (3 * k - 1) / 2) ≤ d := by
  induction fuel generalizing k with
  | zero => simp [pentShifts] at hd
  | succ fuel ih =>
    simp only [pentShifts] at hd
    split_ifs at hd with h1 h2
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact le_rfl
      rcases List.mem_cons.mp hd with rfl | hd
      · exact Nat.mul_le_mul_left s (pent_le_pent_neg k)
      · exact le_trans (Nat.mul_le_mul_left s (pent_mono (Nat.le_succ k))) (ih (k + 1) hd)
    · simp at hd; omega
    · simp at hd

theorem mul_pent_ge (s j : ℕ) (hs : 1 ≤ s) : j ≤ s * (j * (3 * j - 1) / 2) :=
  le_trans (le_pent j) (Nat.le_mul_of_pos_left _ hs)

/-- Membership in `pentShifts`: the shifts `s P_j`, `s P_(-j)` with `j ≥ k` that are `< L`. -/
theorem mem_pentShifts (s L fuel k d : ℕ) (hs : 1 ≤ s) (hfuel : L + 1 ≤ fuel + k) :
    d ∈ pentShifts s L fuel k ↔
      d < L ∧ ∃ j, k ≤ j ∧ (d = s * (j * (3 * j - 1) / 2) ∨ d = s * (j * (3 * j + 1) / 2)) := by
  induction fuel generalizing k with
  | zero =>
    simp only [pentShifts, List.not_mem_nil, false_iff, not_and, not_exists]
    intro hd j hj h
    have h1 := mul_pent_ge s j hs
    have h2 := Nat.mul_le_mul_left s (pent_le_pent_neg j)
    omega
  | succ fuel ih =>
    have hmono : ∀ j, k + 1 ≤ j → s * ((k + 1) * (3 * (k + 1) - 1) / 2) ≤ s * (j * (3 * j - 1) / 2) :=
      fun j hj ↦ Nat.mul_le_mul_left s (pent_mono hj)
    have hkk := Nat.mul_lt_mul_of_pos_left (pent_neg_lt_pent_succ k) (show 0 < s by omega)
    have hneg : ∀ j, s * (j * (3 * j - 1) / 2) ≤ s * (j * (3 * j + 1) / 2) :=
      fun j ↦ Nat.mul_le_mul_left s (pent_le_pent_neg j)
    have hmk : ∀ j, k ≤ j → s * (k * (3 * k - 1) / 2) ≤ s * (j * (3 * j - 1) / 2) :=
      fun j hj ↦ Nat.mul_le_mul_left s (pent_mono hj)
    simp only [pentShifts]
    split_ifs with h1 h2
    · rw [List.mem_cons, List.mem_cons, ih (k + 1) (by omega)]
      constructor
      · rintro (rfl | rfl | ⟨hd, j, hj, hj'⟩)
        · exact ⟨h1, k, le_rfl, Or.inl rfl⟩
        · exact ⟨h2, k, le_rfl, Or.inr rfl⟩
        · exact ⟨hd, j, by omega, hj'⟩
      · rintro ⟨hd, j, hj, hj'⟩
        rcases Nat.eq_or_lt_of_le hj with rfl | hj
        · rcases hj' with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr ⟨hd, j, hj, hj'⟩)
    · rw [List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨h1, k, le_rfl, Or.inl rfl⟩
      · rintro ⟨hd, j, hj, hj'⟩
        rcases Nat.eq_or_lt_of_le hj with rfl | hj
        · rcases hj' with rfl | rfl
          · rfl
          · omega
        · have := hmono j hj; have := hneg j
          rcases hj' with rfl | rfl <;> omega
    · simp only [List.not_mem_nil, false_iff, not_and, not_exists]
      intro hd j hj hj'
      have := hmk j hj; have := hneg j
      rcases hj' with rfl | rfl <;> omega

/-- The shift list of `mulPent`, with `0` for the constant term of `fbar`. -/
def pentList (s L : ℕ) : List ℕ := 0 :: pentShifts s L L 1

theorem mem_pentList (s L d : ℕ) (hs : 1 ≤ s) (hL : 1 ≤ L) :
    d ∈ pentList s L ↔ d < L ∧ s ∣ d ∧ d / s ∈ Set.range pentagonal := by
  rw [pentList, List.mem_cons, mem_pentShifts s L L 1 d hs (by omega)]
  constructor
  · rintro (rfl | ⟨hd, j, hj, hj' | hj'⟩)
    · exact ⟨hL, dvd_zero s, 0, by simp [pentagonal]⟩
    · refine ⟨hd, hj' ▸ dvd_mul_right _ _, j, ?_⟩
      rw [hj', Nat.mul_div_cancel_left _ (by omega), pentagonal_natCast]
    · refine ⟨hd, hj' ▸ dvd_mul_right _ _, -(j : ℤ), ?_⟩
      rw [hj', Nat.mul_div_cancel_left _ (by omega), pentagonal_neg_natCast]
  · rintro ⟨hd, ⟨m, rfl⟩, z, hz⟩
    rw [Nat.mul_div_cancel_left _ (by omega)] at hz
    rcases Int.eq_nat_or_neg z with ⟨j, rfl | rfl⟩
    · rw [pentagonal_natCast] at hz
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · left; simp at hz; simp [← hz]
      · exact Or.inr ⟨hd, j, hj, Or.inl (by rw [hz])⟩
    · rw [pentagonal_neg_natCast] at hz
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · left; simp at hz; simp [← hz]
      · exact Or.inr ⟨hd, j, hj, Or.inr (by rw [hz])⟩

theorem pentShifts_pairwise (s L fuel k : ℕ) (hs : 1 ≤ s) (hk : 1 ≤ k) :
    (pentShifts s L fuel k).Pairwise (· < ·) := by
  induction fuel generalizing k with
  | zero => simp [pentShifts]
  | succ fuel ih =>
    simp only [pentShifts]
    have hlt := Nat.mul_lt_mul_of_pos_left (pent_lt_pent_neg k hk) (show 0 < s by omega)
    have hkk := Nat.mul_lt_mul_of_pos_left (pent_neg_lt_pent_succ k) (show 0 < s by omega)
    split_ifs with h1 h2
    · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (ih (k + 1) (by omega)))
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hlt
        · have := pentShifts_ge s L fuel (k + 1) d hd; omega
      · intro d hd
        have := pentShifts_ge s L fuel (k + 1) d hd; omega
    · simp
    · simp

theorem pentList_nodup (s L : ℕ) (hs : 1 ≤ s) : (pentList s L).Nodup := by
  have hp := pentShifts_pairwise s L L 1 hs le_rfl
  refine (List.Pairwise.cons ?_ hp).nodup
  intro d hd
  have := pentShifts_ge s L L 1 d hd
  simp at this; omega

/-- `B * fbar(q^s) mod q^L`. -/
def mulPent (B s L : ℕ) : ℕ := xorShifts B L (pentList s L) 0

theorem testBit_xorShifts_ge (B L n : ℕ) (ds : List ℕ) (hn : L ≤ n) :
    (xorShifts B L ds 0).testBit n = false := by
  have h := b2z_testBit_xorShifts B L n ds 0
  have : ∀ d ∈ ds, b2z (decide (d ≤ n) && B.testBit (n - d) && decide (n < L)) = 0 := by
    intro d _; simp [show ¬ n < L by omega]
  rw [List.sum_eq_zero (by simpa using this)] at h
  simp only [Nat.zero_testBit, b2z_false, add_zero] at h
  revert h; cases (xorShifts B L ds 0).testBit n <;> decide

open Classical in
theorem coeff_expand_fbar (s : ℕ) (hs : s ≠ 0) (d : ℕ) :
    coeff d (expand s hs fbar) = if s ∣ d ∧ d / s ∈ Set.range pentagonal then 1 else 0 := by
  rw [coeff_expand, coeff_fbar]
  by_cases h1 : s ∣ d <;> by_cases h2 : d / s ∈ Set.range pentagonal <;> simp [h1, h2]

/-- Correctness of `mulPent`. -/
theorem rep_mulPent (B L s : ℕ) (ψ : (ZMod 2)⟦X⟧) (hs : s ≠ 0) (hB : Rep B L ψ) :
    Rep (mulPent B s L) L (ψ * expand s hs fbar) := by
  classical
  intro n
  by_cases hn : n < L
  · have hL : 1 ≤ L := by omega
    have key := b2z_testBit_xorShifts B L n (pentList s L) 0
    simp only [Nat.zero_testBit, b2z_false, zero_add] at key
    have hterm : ∀ d, b2z (decide (d ≤ n) && B.testBit (n - d) && decide (n < L)) =
        if d ∈ Finset.range (n + 1) then coeff (n - d) ψ else 0 := by
      intro d
      rw [hB (n - d)]
      by_cases hd : d ≤ n
      · simp [hd, hn, show n - d < L by omega, Finset.mem_range, Nat.lt_succ_of_le hd,
          b2z_decide_eq_one]
      · simp [hd, Finset.mem_range, show ¬ d < n + 1 by omega]
    simp only [hterm] at key
    rw [← List.sum_toFinset _ (pentList_nodup s L (by omega)), Finset.sum_ite_mem] at key
    have hc : coeff n (ψ * expand s hs fbar) =
        ∑ d ∈ Finset.range (n + 1) ∩ (pentList s L).toFinset, coeff (n - d) ψ := by
      rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [coeff_expand_fbar]
      rw [← Finset.sum_ite_mem]
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      have hdn : d < L := by rw [Finset.mem_range] at hd; omega
      have hm : d ∈ (pentList s L).toFinset ↔ s ∣ d ∧ d / s ∈ Set.range pentagonal := by
        rw [List.mem_toFinset, mem_pentList s L d (by omega) hL]; simp [hdn]
      by_cases h : s ∣ d ∧ d / s ∈ Set.range pentagonal
      · rw [ite_eq_left h, ite_eq_left (hm.mpr h), one_mul]
      · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h (hm.mp h')), zero_mul]
    rw [Finset.inter_comm] at key
    rw [hc, ← key, decide_eq_true hn, Bool.true_and]
    unfold mulPent
    cases (xorShifts B L (pentList s L) 0).testBit n <;> rfl
  · rw [mulPent, testBit_xorShifts_ge B L n _ (by omega)]
    simp [hn]

theorem fbar_pow_two_pow (i : ℕ) : fbar ^ (2 ^ i) = expand (2 ^ i) (two_pow_ne_zero' i) fbar :=
  pow_two_pow_eq_expand fbar i

theorem rep_mulPent_two_pow (B L i : ℕ) (ψ : (ZMod 2)⟦X⟧) (hB : Rep B L ψ) :
    Rep (mulPent B (2 ^ i) L) L (ψ * fbar ^ (2 ^ i)) := by
  rw [fbar_pow_two_pow]; exact rep_mulPent B L _ ψ _ hB

theorem rep_one (L : ℕ) (hL : 1 ≤ L) : Rep 1 L 1 := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.testBit_zero]; omega
  · have : (1 : ℕ).testBit n = false := by
      rw [Nat.testBit_eq_false_of_lt]; exact Nat.one_lt_two_pow hn.ne'
    simp [this, coeff_one, hn.ne']

/-- Bits of `ψ * fbar ^ (2^i * τ)` from the bits `B` of `ψ`, one binary digit of `τ` at a time. -/
def mulDigits (L : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, B => B
  | fuel + 1, τ, i, B =>
    mulDigits L fuel (τ / 2) (i + 1) (if τ % 2 = 1 then mulPent B (2 ^ i) L else B)

theorem rep_mulDigits (L fuel τ i B : ℕ) (ψ : (ZMod 2)⟦X⟧) (hB : Rep B L ψ)
    (hτ : τ < 2 ^ fuel) : Rep (mulDigits L fuel τ i B) L (ψ * fbar ^ (2 ^ i * τ)) := by
  induction fuel generalizing τ i B ψ with
  | zero =>
    have : τ = 0 := by simpa using hτ
    subst this; simpa [mulDigits] using hB
  | succ fuel ih =>
    rw [mulDigits]
    have hsplit : 2 ^ i * τ = 2 ^ i * (τ % 2) + 2 ^ (i + 1) * (τ / 2) := by
      conv_lhs => rw [← Nat.mod_add_div τ 2]
      ring
    have hB' : Rep (if τ % 2 = 1 then mulPent B (2 ^ i) L else B) L
        (ψ * fbar ^ (2 ^ i * (τ % 2))) := by
      rcases Nat.mod_two_eq_zero_or_one τ with h | h
      · simpa [h] using hB
      · simpa [h] using rep_mulPent_two_pow B L i ψ hB
    have := ih (τ / 2) (i + 1) _ _ hB' (by rw [pow_succ] at hτ; omega)
    rwa [mul_assoc, ← pow_add, ← hsplit] at this

/-- Bits of `fbar ^ τ mod q^L`, for `τ < 2^20`. -/
def powBits (τ L : ℕ) : ℕ := mulDigits L 20 τ 0 1

theorem rep_powBits (τ L : ℕ) (hL : 1 ≤ L) (hτ : τ < 2 ^ 20) : Rep (powBits τ L) L (fbar ^ τ) := by
  have := rep_mulDigits L 20 τ 0 1 1 (rep_one L hL) hτ
  simpa [powBits] using this

/-- From bits to coefficients. -/
theorem Rep.coeff_eq_one_iff {B L : ℕ} {ψ : (ZMod 2)⟦X⟧} (h : Rep B L ψ) {n : ℕ} (hn : n < L) :
    coeff n ψ = 1 ↔ B.testBit n = true := by
  rw [h n]; simp [hn]

theorem Rep.testBit_ge {B L : ℕ} {ψ : (ZMod 2)⟦X⟧} (h : Rep B L ψ) {n : ℕ} (hn : L ≤ n) :
    B.testBit n = false := by
  rw [h n]; simp [show ¬ n < L by omega]

end KeithZanello
