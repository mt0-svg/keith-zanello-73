import KZ73.Tree

/-!
# The finite part of the paper's Lemma 11 at `p = 73`

For each of the eighteen elements `t ≥ 5` of `E73`, `heckeCoeff 73 t m` is even for
`1 ≤ m ≤ 48 (t + 1)` (kernel evaluation on the bits of `fbar ^ t mod q^(2^15)`; the largest index
used is `(73 · 48 · 204 - 203) / 24 = 29775 < 2^15`). Under `SturmHypothesis` this gives
`T_73 H_t ≡ 0 (mod 2)`, hence condition (G) (last step of the proof of Lemma 11).
-/

open PowerSeries

namespace KeithZanello

/-- Parity of `a t m`, from the bits `B` of `fbar ^ t`. -/
def abit (t B m : ℕ) : Bool := decide (t ≤ m) && (m - t) % 24 == 0 && B.testBit ((m - t) / 24)

/-- Parity of `heckeCoeff 73 t m`. -/
def heckeBit (t B m : ℕ) : Bool := abit t B (73 * m) ^^ (m % 73 == 0 && abit t B (m / 73))

/-- `heckeBit t B m = false` for `1 ≤ m ≤ n`. -/
def sturmLoop (t B : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => !heckeBit t B (n + 1) && sturmLoop t B n

/-- The test of Lemma 11 at `p = 73`, up to the Sturm bound `48 (t + 1)`. -/
def sturmTest (t : ℕ) : Bool := sturmLoop t (powBitsH t 15) (48 * (t + 1))

theorem even_iff_zmod (z : ℤ) : Even z ↔ (z : ZMod 2) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, even_iff_two_dvd]; norm_num

theorem a_zmod {t B L m : ℕ} (hB : Rep B L (fbar ^ t)) (hm : m < 24 * L + t) :
    ((a t m : ℤ) : ZMod 2) = b2z (abit t B m) := by
  unfold a abit
  by_cases h1 : t ≤ m ∧ 24 ∣ m - t
  · rw [ite_eq_left h1]
    have h24 : (m - t) % 24 = 0 := Nat.mod_eq_zero_of_dvd h1.2
    have hn : (m - t) / 24 < L := by omega
    rw [← coeff_fbar_pow, hB, decide_eq_true hn]
    simp [h1.1, h24, b2z_decide_eq_one]
  · rw [ite_eq_right h1]
    have : (decide (t ≤ m) && (m - t) % 24 == 0) = false := by
      by_cases h2 : t ≤ m
      · have : ¬ 24 ∣ m - t := fun h ↦ h1 ⟨h2, h⟩
        simp [h2, Nat.dvd_iff_mod_eq_zero.not.mp this]
      · simp [h2]
    simp [this]

theorem heckeCoeff_zmod {t B L m : ℕ} (hB : Rep B L (fbar ^ t)) (hm : 73 * m < 24 * L + t) :
    ((heckeCoeff 73 t m : ℤ) : ZMod 2) = b2z (heckeBit t B m) := by
  unfold heckeCoeff heckeBit
  rw [b2z_xor, Int.cast_add, a_zmod hB hm]
  congr 1
  by_cases h : 73 ∣ m
  · rw [ite_eq_left h, a_zmod hB (by omega)]
    simp [Nat.mod_eq_zero_of_dvd h]
  · rw [ite_eq_right h]
    have h' : ¬ m % 73 = 0 := fun h0 ↦ h (Nat.dvd_of_mod_eq_zero h0)
    simp [h', b2z]

theorem even_heckeCoeff_of_sturmLoop {t B L : ℕ} (hB : Rep B L (fbar ^ t)) :
    ∀ n, 73 * n < 24 * L + t → sturmLoop t B n = true →
      ∀ m, 1 ≤ m → m ≤ n → Even (heckeCoeff 73 t m) := by
  intro n
  induction n with
  | zero => intro _ _ m h1 h2; omega
  | succ n ih =>
    intro hL hs m h1 h2
    simp only [sturmLoop, Bool.and_eq_true, Bool.not_eq_true'] at hs
    rcases Nat.lt_or_ge m (n + 1) with hm | hm
    · exact ih (by omega) hs.2 m h1 (by omega)
    · obtain rfl : m = n + 1 := by omega
      rw [even_iff_zmod, heckeCoeff_zmod hB hL, hs.1]; rfl

theorem even_heckeCoeff_of_sturmTest {t : ℕ} (ht : t ≤ 203) (h : sturmTest t = true) :
    ∀ m, 1 ≤ m → m ≤ 48 * (t + 1) → Even (heckeCoeff 73 t m) :=
  even_heckeCoeff_of_sturmLoop (rep_powBitsH t 15 (by norm_num; omega)) _ (by norm_num; omega) h

theorem sturmTest_5 : sturmTest 5 = true := by decide +kernel
theorem sturmTest_7 : sturmTest 7 = true := by decide +kernel
theorem sturmTest_9 : sturmTest 9 = true := by decide +kernel
theorem sturmTest_11 : sturmTest 11 = true := by decide +kernel
theorem sturmTest_13 : sturmTest 13 = true := by decide +kernel
theorem sturmTest_15 : sturmTest 15 = true := by decide +kernel
theorem sturmTest_17 : sturmTest 17 = true := by decide +kernel
theorem sturmTest_19 : sturmTest 19 = true := by decide +kernel
theorem sturmTest_21 : sturmTest 21 = true := by decide +kernel
theorem sturmTest_23 : sturmTest 23 = true := by decide +kernel
theorem sturmTest_51 : sturmTest 51 = true := by decide +kernel
theorem sturmTest_55 : sturmTest 55 = true := by decide +kernel
theorem sturmTest_59 : sturmTest 59 = true := by decide +kernel
theorem sturmTest_61 : sturmTest 61 = true := by decide +kernel
theorem sturmTest_65 : sturmTest 65 = true := by decide +kernel
theorem sturmTest_69 : sturmTest 69 = true := by decide +kernel
theorem sturmTest_199 : sturmTest 199 = true := by decide +kernel
theorem sturmTest_203 : sturmTest 203 = true := by decide +kernel

theorem sturmTest_all : ∀ t ∈ centreList, sturmTest t = true := by
  intro t ht
  simp only [centreList, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  exacts [sturmTest_5, sturmTest_7, sturmTest_9, sturmTest_11, sturmTest_13, sturmTest_15,
    sturmTest_17, sturmTest_19, sturmTest_21, sturmTest_23, sturmTest_51, sturmTest_55,
    sturmTest_59, sturmTest_61, sturmTest_65, sturmTest_69, sturmTest_199, sturmTest_203]

end KeithZanello
