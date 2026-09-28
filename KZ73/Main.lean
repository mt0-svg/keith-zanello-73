import KZ73.TreeCert
import KZ73.SparseCheck
import KZ73.SturmCheck

/-!
# The disproof of Conjecture B at `p = 73`

* `condG_one`, `condG_three`: condition (G) for `t = 1` (Euler) and `t = 3` (Jacobi), so `f₁` and
  `f₁^3` are `(73, r_t)`-even (the paper's Lemma 10), unconditionally.
* `not_isP2Even_of_not_centre`: every odd `t ∉ E73` whose residue modulo `2^14` is not one of the
  eighteen centres is not `73^2`-even, unconditionally.
* `mainClaimG`: condition (G) for the eighteen centres implies Theorem 1.
* `condG_of_sturm`, `mainClaim`: the paper's Lemma 11 (`SturmHypothesis`) implies (G) for the
  centres, hence Theorem 1; `not_conjectureB`: it implies that Conjecture B is false.
-/

open PowerSeries

namespace KeithZanello

/-! ## Condition (G) and the Hecke operator -/

/-- Last step of the proof of the paper's Lemma 11: `T_73 A_t ≡ 0 (mod 2)` gives (G). -/
theorem condG_of_hecke {t : ℕ} (h : ∀ m, 1 ≤ m → Even (heckeCoeff 73 t m)) : CondG 73 t := by
  intro N h1 h2
  obtain ⟨m, hm⟩ := h1
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exfalso; apply h2; rw [hm]; simp
    · exact hpos
  have hN : c t N = heckeCoeff 73 t m := by
    unfold heckeCoeff a
    have ht : t ≤ 73 * m := by omega
    have h24 : 24 ∣ 73 * m - t := ⟨N, by omega⟩
    have hdiv : (73 * m - t) / 24 = N := by omega
    have hnd : ¬ 73 ∣ m := by
      rintro ⟨k, rfl⟩; apply h2; rw [hm]; exact ⟨k, by ring⟩
    rw [ite_eq_left ⟨ht, h24⟩, hdiv, ite_eq_right hnd, add_zero]
  rw [hN]; exact h m hm1

/-- `f₁` modulo 2 is supported on the pentagonal numbers `N`, where `24 N + 1 = (6k - 1)^2`. -/
theorem condG_one : CondG 73 1 := by
  classical
  intro N h1 h2
  rw [even_c_iff, pow_one, coeff_fbar]
  split_ifs with hN
  · exfalso
    obtain ⟨k, rfl⟩ := hN
    have hsq : ((24 * pentagonal k + 1 : ℕ) : ℤ) = (6 * k - 1) ^ 2 := by
      push_cast; linear_combination 12 * two_mul_natCast_pentagonal k
    have hp : Prime (73 : ℤ) := Nat.prime_iff_prime_int.mp (by decide)
    have hd : (73 : ℤ) ∣ (6 * k - 1) ^ 2 := by rw [← hsq]; exact_mod_cast h1
    have hd2 : (73 : ℤ) ^ 2 ∣ (6 * k - 1) ^ 2 := pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hd) 2
    apply h2
    rw [← hsq] at hd2; exact_mod_cast hd2
  · rfl

/-- `f₁^3` modulo 2 is supported on the triangular numbers `N`, where `24 N + 3 = 3 (2k + 1)^2`. -/
theorem condG_three : CondG 73 3 := by
  classical
  intro N h1 h2
  rw [even_c_iff, coeff_fbar_pow_three]
  split_ifs with hN
  · exfalso
    obtain ⟨k, rfl⟩ := hN
    have hev : k * (k + 1) / 2 * 2 = k * (k + 1) := Nat.div_mul_cancel (Nat.even_mul_succ_self k).two_dvd
    have hsq : 24 * (k * (k + 1) / 2) + 3 = 3 * (2 * k + 1) ^ 2 := by nlinarith
    have hp : Nat.Prime 73 := by decide
    rw [hsq] at h1 h2
    have hd : 73 ∣ (2 * k + 1) ^ 2 := by
      rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
      · exact absurd (Nat.le_of_dvd (by norm_num) h) (by norm_num)
      · exact h
    exact h2 (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hd) 2) 3)
  · rfl

theorem rt_lt (t : ℕ) : rt t < 73 ^ 2 := by rw [pow_two_73]; exact Nat.mod_lt _ (by norm_num)

theorem rt_eq (t : ℕ) : 222 * t % 73 ^ 2 = rt t := by rw [pow_two_73]; rfl

/-! ## Uniqueness of the base at the centres -/

/-- The level of the ball of each centre. -/
def centreLevel (t : ℕ) : ℕ := if t = 199 ∨ t = 203 then 16 else 14

theorem centres_ok :
    ∀ t ∈ centreList, centreTest t (powBitsH t (centreLevel t)) (2 ^ centreLevel t) = true := by
  decide +kernel

theorem centreList_iff (t : ℕ) : t ∈ centreList ↔ t ∈ E73 ∧ 5 ≤ t := by
  constructor
  · exact mem_E73_of_centreList t
  · rintro ⟨h1, h2⟩; revert t; decide

theorem base_unique {t : ℕ} (ht : t ∈ E73) (h5 : 5 ≤ t) (hG : CondG 73 t) {r : ℕ} (hr : r < 73 ^ 2)
    (hb : IsEvenWithBase 73 t r) : r = 222 * t % 73 ^ 2 := by
  have hm := (centreList_iff t).mpr ⟨ht, h5⟩
  have hlt : t < 2 ^ centreLevel t := by
    simp only [centreList, List.mem_cons, List.not_mem_nil, or_false] at hm
    unfold centreLevel; split_ifs <;> norm_num <;> omega
  obtain ⟨hi, hii⟩ := centre_of_centreTest (rep_powBitsH t _ hlt) (centres_ok t hm)
  obtain ⟨Na, hNa1, -, hNa3, hNa4⟩ := hii
  rw [pow_two_73] at hr
  have e1 := base_eq_of_centre hi hNa1 hNa3 hNa4 hr hb
  have e2 := base_eq_of_centre hi hNa1 hNa3 hNa4 (by have := rt_lt t; rwa [pow_two_73] at this)
    (evenWithBase_rt_of_condG hG)
  rw [rt_eq, e1, e2]

/-! ## Main theorems -/

/-- Unconditional badness: an odd `t ∉ E73` whose residue modulo `2^14` is not a centre is not
`73^2`-even. -/
theorem not_isP2Even_of_not_centre {t : ℕ} (hodd : Odd t) (hE : t ∉ E73)
    (hc : t % 16384 ∉ centreList) : ¬ IsP2Even 73 t := by
  apply not_isP2Even_of_closed
  refine closed_of_not_mem_E73 condS1 condS3 (Nat.odd_iff.mp hodd) hE ?_
  intro s hs h5 hts
  exact absurd (hts ▸ (centreList_iff s).mpr ⟨hs, h5⟩) hc

/-- The paper's Theorem 1, from condition (G) for the eighteen centres. -/
theorem mainClaimG : MainClaimG := by
  intro hG
  have hG' : ∀ t ∈ E73, CondG 73 t := by
    intro t ht
    by_cases h5 : 5 ≤ t
    · exact hG t ht h5
    · have : t = 1 ∨ t = 3 := by revert t; decide
      rcases this with rfl | rfl
      · exact condG_one
      · exact condG_three
  refine ⟨?_, fun t ht ↦ ?_, fun t ht h5 r hr hb ↦ base_unique ht h5 (hG t ht h5) hr hb⟩
  · ext t
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro ⟨hodd, hp⟩
      by_contra hE
      refine not_isP2Even_of_closed (closed_of_not_mem_E73 condS1 condS3
        (Nat.odd_iff.mp hodd) hE ?_) hp
      intro s hs h5 _
      exact hG s hs h5
    · intro ht
      refine ⟨?_, rt t, rt_lt t, evenWithBase_rt_of_condG (hG' t ht)⟩
      revert t; decide
  · rw [rt_eq]; exact evenWithBase_rt_of_condG (hG' t ht)

theorem sturmHypothesis73_of_sturmHypothesis (hS : SturmHypothesis) : SturmHypothesis73 := by
  intro t ht h5
  have hodd : Odd t := by revert t; decide
  exact hS 73 t (by decide) (by norm_num) hodd

/-- The finite checks of `KZ73/SturmCheck.lean` turn the instance of Sturm's theorem into
`T_73 H_t ≡ 0 (mod 2)` for the eighteen centres. -/
theorem hecke73_of_sturmHypothesis73 (hS : SturmHypothesis73) : Hecke73 := by
  intro t ht h5
  have hm := (centreList_iff t).mpr ⟨ht, h5⟩
  have h203 : t ≤ 203 := by
    simp only [centreList, List.mem_cons, List.not_mem_nil, or_false] at hm; omega
  exact hS t ht h5 (even_heckeCoeff_of_sturmTest h203 (sturmTest_all t hm))

/-- `T_73 H_t ≡ 0 (mod 2)` for the eighteen centres implies Theorem 1. -/
theorem theorem1_of_hecke73 (h : Hecke73) : Theorem1 :=
  mainClaimG fun t ht h5 ↦ condG_of_hecke (h t ht h5)

/-- Under the paper's Lemma 11, condition (G) holds for the eighteen centres. -/
theorem condG_of_sturm (hS : SturmHypothesis) : ∀ t ∈ E73, 5 ≤ t → CondG 73 t :=
  fun t ht h5 ↦ condG_of_hecke
    (hecke73_of_sturmHypothesis73 (sturmHypothesis73_of_sturmHypothesis hS) t ht h5)

/-- Theorem 1 from the instance of Sturm's theorem at `p = 73` for the eighteen centres. -/
theorem theorem1_of_sturmHypothesis73 (hS : SturmHypothesis73) : Theorem1 :=
  theorem1_of_hecke73 (hecke73_of_sturmHypothesis73 hS)

/-- Conjecture B is false, given the instance of Sturm's theorem at `p = 73`. -/
theorem not_conjectureB_of_sturmHypothesis73 (hS : SturmHypothesis73) : ¬ ConjectureB :=
  not_conjectureB_of_theorem1 (theorem1_of_sturmHypothesis73 hS)

/-- **Main theorem**: the paper's Lemma 11 implies the paper's Theorem 1. -/
theorem mainClaim : MainClaim := fun hS ↦ mainClaimG (condG_of_sturm hS)

/-- **Conjecture B is false**, given the paper's Lemma 11 (`SturmHypothesis`). -/
theorem not_conjectureB (hS : SturmHypothesis) : ¬ ConjectureB :=
  not_conjectureB_of_theorem1 (mainClaim hS)

/-- The same from condition (G) for the eighteen centres. -/
theorem not_conjectureB_of_condG (hG : ∀ t ∈ E73, 5 ≤ t → CondG 73 t) : ¬ ConjectureB :=
  not_conjectureB_of_theorem1 (mainClaimG hG)

end KeithZanello
