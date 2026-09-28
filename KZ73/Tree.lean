import KZ73.Sparse

/-!
# The partition of the odd 2-adic integers (the paper's Proposition 17, at `p = 73`)

`GoodClass τ h` says that every `T ≡ τ (mod 2^h)` outside `E73` is closed, hence not
`73^2`-even (Lemma 7), provided condition (G) holds for the centre `t` with `T ≡ t (mod 2^14)`, if
any (`CentreHyp T`). A ball `B(τ, h)` is certified by `leafTest` as closed (a pair in every
class below `2^h`), as a centre (Lemma 13, for the eighteen elements `t ≥ 5` of `E73`), or as
sparse (Lemma 15, for the balls around `1` and `3`); otherwise it is split in two.

The search starts at level `14` (`8192` balls). The products `fbar ^ τ mod q^(2^14)` are shared
along a traversal of the binary digits of `τ` from the lowest one (`sweep`); the few balls split
at level `14` are handled by `checkDeep`, which recomputes `fbar ^ τ mod q^(2^h)` for `h ≤ 17`.
-/

open PowerSeries

namespace KeithZanello

/-- Condition (G) for the centre in the class of `T` modulo `2^14`, if there is one. -/
def CentreHyp (T : ℕ) : Prop := ∀ t ∈ E73, 5 ≤ t → T % 16384 = t → CondG 73 t

/-- Every `T ≡ τ (mod 2^h)` outside `E73` satisfying `CentreHyp T` is closed. -/
def GoodClass (τ h : ℕ) : Prop :=
  ∀ T, T % 2 ^ h = τ → T ∉ E73 → CentreHyp T → Closed (fbar ^ T)

theorem mod_two_pow_succ_cases {T i τ : ℕ} (h : T % 2 ^ i = τ) :
    T % 2 ^ (i + 1) = τ ∨ T % 2 ^ (i + 1) = τ + 2 ^ i := by
  have h1 : T % 2 ^ (i + 1) % 2 ^ i = τ := by
    rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_succ i))]; exact h
  have hP : 0 < 2 ^ i := Nat.two_pow_pos i
  have h2 : T % 2 ^ (i + 1) < 2 * 2 ^ i := by
    rw [← pow_succ']; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have h3 := Nat.mod_add_div (T % 2 ^ (i + 1)) (2 ^ i)
  have h4 : T % 2 ^ (i + 1) / 2 ^ i < 2 := by
    rw [Nat.div_lt_iff_lt_mul hP]; exact h2
  generalize T % 2 ^ (i + 1) = r at *
  generalize 2 ^ i = P at *
  generalize r / P = q at h3 h4
  interval_cases q
  · left; omega
  · right; omega

theorem goodClass_of_split {τ h : ℕ} (h1 : GoodClass τ (h + 1)) (h2 : GoodClass (τ + 2 ^ h) (h + 1)) :
    GoodClass τ h := by
  intro T hT hTE hC
  rcases mod_two_pow_succ_cases hT with h' | h'
  · exact h1 T h' hTE hC
  · exact h2 T h' hTE hC

theorem goodClass_of_forall {τ₀ i h : ℕ} (hih : i ≤ h)
    (H : ∀ τ < 2 ^ h, τ % 2 ^ i = τ₀ → GoodClass τ h) : GoodClass τ₀ i := by
  intro T hT hTE hC
  refine H (T % 2 ^ h) (Nat.mod_lt _ (Nat.two_pow_pos h)) ?_ T rfl hTE hC
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hih)]; exact hT

theorem rep_of_mod {B h τ T : ℕ} (hB : Rep B (2 ^ h) (fbar ^ τ)) (hT : T % 2 ^ h = τ) :
    Rep B (2 ^ h) (fbar ^ T) := by
  intro n
  rw [hB n]
  by_cases hn : n < 2 ^ h
  · rw [coeff_fbar_pow_mod T h n hn, hT]
  · simp [hn]

/-! ## The leaf test -/

/-- The eighteen elements `t ≥ 5` of `E73`. -/
def centreList : List ℕ := [5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 51, 55, 59, 61, 65, 69, 199, 203]

theorem mem_E73_of_centreList : ∀ t ∈ centreList, t ∈ E73 ∧ 5 ≤ t := by decide

/-- Certificate of a ball `B(τ, h)`, given the bits `B` of `fbar ^ τ mod q^(2^h)`. -/
def leafTest (τ h B : ℕ) : Bool :=
  closedTest B (2 ^ h) ||
  (decide (14 ≤ h) && centreList.contains τ && centreTest τ B (2 ^ h)) ||
  (decide (13 ≤ h) && τ % 8192 == 1) ||
  (decide (11 ≤ h) && τ % 2048 == 3)

section Sound

variable (hS1 : CondS1) (hS3 : CondS3)
include hS1 hS3

theorem goodClass_of_leafTest {τ h B : ℕ} (hτ : τ < 2 ^ h) (hB : Rep B (2 ^ h) (fbar ^ τ))
    (ht : leafTest τ h B = true) : GoodClass τ h := by
  intro T hT hTE hC
  simp only [leafTest, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_iff_mem] at ht
  rcases ht with ((hc | ⟨⟨h14, hm⟩, hc⟩) | ⟨h13, h1⟩) | ⟨h11, h3⟩
  · exact closed_of_closedTest (rep_of_mod hB hT) hc
  · obtain ⟨hE, h5⟩ := mem_E73_of_centreList τ hm
    obtain ⟨hi, hii⟩ := centre_of_centreTest hB hc
    have hτ14 : τ < 16384 := by simp [centreList] at hm; omega
    have hT14 : T % 16384 = τ := by
      rw [show (16384 : ℕ) = 2 ^ 14 by norm_num, ← Nat.mod_mod_of_dvd T (pow_dvd_pow 2 h14), hT,
        Nat.mod_eq_of_lt (by norm_num; omega)]
    exact closed_of_centre hτ (hC τ hE h5 hT14) hi hii hT (fun h ↦ hTE (h ▸ hE))
  · refine closed_of_sparse1 hS1 ?_ (fun h ↦ hTE (h ▸ (by decide : 1 ∈ E73)))
    rw [← Nat.mod_mod_of_dvd T (pow_dvd_pow 2 h13), hT]; exact h1
  · refine closed_of_sparse3 hS3 ?_ (fun h ↦ hTE (h ▸ (by decide : 3 ∈ E73)))
    rw [← Nat.mod_mod_of_dvd T (pow_dvd_pow 2 h11), hT]; exact h3

end Sound

/-! ## Deep balls -/

/-- Bits of `fbar ^ τ mod q^(2^h)`, for `τ < 2^h`. -/
def powBitsH (τ h : ℕ) : ℕ := mulDigits (2 ^ h) h τ 0 1

theorem rep_powBitsH (τ h : ℕ) (hτ : τ < 2 ^ h) : Rep (powBitsH τ h) (2 ^ h) (fbar ^ τ) := by
  have := rep_mulDigits (2 ^ h) h τ 0 1 1 (rep_one _ Nat.one_le_two_pow) hτ
  simpa [powBitsH] using this

/-- Certify `B(τ, h)`, splitting at most `fuel - 1` times. -/
def checkDeep : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, τ, h =>
    leafTest τ h (powBitsH τ h) || (checkDeep fuel τ (h + 1) && checkDeep fuel (τ + 2 ^ h) (h + 1))

theorem goodClass_of_checkDeep (hS1 : CondS1) (hS3 : CondS3) : ∀ fuel τ h, τ < 2 ^ h → checkDeep fuel τ h = true → GoodClass τ h := by
  intro fuel
  induction fuel with
  | zero => intro τ h _ hc; simp [checkDeep] at hc
  | succ fuel ih =>
    intro τ h hτ hc
    simp only [checkDeep, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with hc | ⟨h1, h2⟩
    · exact goodClass_of_leafTest hS1 hS3 hτ (rep_powBitsH τ h hτ) hc
    · have hτ' : τ + 2 ^ h < 2 ^ (h + 1) := by rw [pow_succ]; omega
      exact goodClass_of_split (ih τ (h + 1) (by rw [pow_succ]; omega) h1) (ih _ _ hτ' h2)

/-! ## The sweep at level 14 -/

/-- Traverse the digits `i, …, 13` of `τ`; `B` holds the bits of `fbar ^ τ mod q^(2^14)`. -/
def sweep : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, B, τ, _ => leafTest τ 14 B || checkDeep 4 τ 14
  | fuel + 1, B, τ, i => sweep fuel B τ (i + 1) && sweep fuel (mulPent B (2 ^ i) 16384) (τ + 2 ^ i) (i + 1)

theorem goodClass_of_sweep (hS1 : CondS1) (hS3 : CondS3) :
    ∀ fuel B τ i, i + fuel = 14 → τ < 2 ^ i → Rep B 16384 (fbar ^ τ) →
      sweep fuel B τ i = true → GoodClass τ i := by
  intro fuel
  induction fuel with
  | zero =>
    intro B τ i hi hτ hB hs
    obtain rfl : i = 14 := by omega
    simp only [sweep, Bool.or_eq_true] at hs
    rcases hs with hs | hs
    · exact goodClass_of_leafTest hS1 hS3 hτ hB hs
    · exact goodClass_of_checkDeep hS1 hS3 4 τ 14 hτ hs
  | succ fuel ih =>
    intro B τ i hi hτ hB hs
    simp only [sweep, Bool.and_eq_true] at hs
    have hτ' : τ + 2 ^ i < 2 ^ (i + 1) := by rw [pow_succ]; omega
    have hB' : Rep (mulPent B (2 ^ i) 16384) 16384 (fbar ^ (τ + 2 ^ i)) := by
      rw [pow_add]; exact rep_mulPent_two_pow B 16384 i _ hB
    exact goodClass_of_split (ih B τ (i + 1) (by omega) (by rw [pow_succ]; omega) hB hs.1)
      (ih _ _ (i + 1) (by omega) hτ' hB' hs.2)

/-- The sweep of the balls `B(τ + 128 s, 14)`, `s < 128`, for `τ < 128`. -/
def sweepFrom (τ : ℕ) : Bool := sweep 7 (mulDigits 16384 7 τ 0 1) τ 7

theorem goodClass_of_sweepFrom (hS1 : CondS1) (hS3 : CondS3)
    {τ : ℕ} (hτ : τ < 128) (h : sweepFrom τ = true) : GoodClass τ 7 := by
  have hB := rep_mulDigits 16384 7 τ 0 1 1 (rep_one _ (by norm_num)) (by norm_num; omega)
  simp only [one_mul, pow_zero] at hB
  exact goodClass_of_sweep hS1 hS3 7 _ τ 7 rfl (by norm_num; omega) hB h

end KeithZanello
