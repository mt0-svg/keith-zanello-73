import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import KZ73.Modular.P2M.Sturm

/-!
# Sturm's bound on `Γ₀(9)` (complex version)

`[SL₂(ℤ) : Γ₀(9)] ≤ 12`, so a form of weight `k` on `Γ₀(9)` whose `q`-expansion coefficients of
index `≤ k` vanish is zero.

The index bound: the left coset `γ Γ₀(9)` is determined by the first column of `γ` in
`P¹(ℤ/9ℤ)`, which is `(1 : c)` for some `c ∈ ℤ/9ℤ` or `(3a : 1)` for some `a ∈ ℤ/3ℤ`. The
matrices `!![1, 0; c, 1]` and `!![3a, -1; 1, 0]` therefore represent all twelve cosets.
-/

open UpperHalfPlane
open scoped MatrixGroups

namespace KeithZanello.Modular

/-- Coset representative with first column `(1, c)`. -/
def gammaNineRepL (c : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

/-- Coset representative with first column `(a, 1)`. -/
def gammaNineRepU (a : ℤ) : SL(2, ℤ) :=
  ⟨!![a, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

/-- Every primitive pair `(x, z)` modulo `9` is equivalent to `(1, c)` or `(3a, 1)`. -/
theorem zmod_nine_cover : ∀ x z : ZMod 9, (x.val % 3 ≠ 0 ∨ z.val % 3 ≠ 0) →
    (∃ c : Fin 9, z = ((c : ℕ) : ZMod 9) * x) ∨
      (∃ a : Fin 3, x = ((3 * (a : ℕ) : ℕ) : ZMod 9) * z) := by
  decide

/-- The coset map from the twelve representatives is surjective. -/
theorem gammaNine_cosets_surjective :
    Function.Surjective (fun i : Fin 9 ⊕ Fin 3 ↦ (Sum.elim
      (fun c : Fin 9 ↦ gammaNineRepL (c : ℕ)) (fun a : Fin 3 ↦ gammaNineRepU (3 * (a : ℕ))) i :
        SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 9)) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H γ =>
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  have hprim : ((γ 0 0 : ℤ) : ZMod 9).val % 3 ≠ 0 ∨ ((γ 1 0 : ℤ) : ZMod 9).val % 3 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hx : ((((γ 0 0 : ℤ) : ZMod 9).val : ℕ) : ℤ) = γ 0 0 % 9 := ZMod.val_intCast _
    have hz : ((((γ 1 0 : ℤ) : ZMod 9).val : ℕ) : ℤ) = γ 1 0 % 9 := ZMod.val_intCast _
    have h3x : (3 : ℤ) ∣ γ 0 0 := by omega
    have h3z : (3 : ℤ) ∣ γ 1 0 := by omega
    have : (3 : ℤ) ∣ 1 := by
      rw [← hdet]
      exact dvd_sub (h3x.mul_right _) (h3z.mul_left _)
    omega
  rcases zmod_nine_cover _ _ hprim with ⟨c, hc⟩ | ⟨a, ha⟩
  · refine ⟨Sum.inl c, ?_⟩
    simp only [Sum.elim_inl]
    rw [QuotientGroup.eq, CongruenceSubgroup.Gamma0_mem, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [gammaNineRepL, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hc]
    ring
  · refine ⟨Sum.inr a, ?_⟩
    simp only [Sum.elim_inr]
    rw [QuotientGroup.eq, CongruenceSubgroup.Gamma0_mem, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [gammaNineRepU, Matrix.mul_apply, Fin.sum_univ_two]
    rw [ha]
    push_cast
    ring

theorem Gamma0_nine_index_le : (CongruenceSubgroup.Gamma0 9).index ≤ 12 := by
  have := Nat.card_le_card_of_surjective _ gammaNine_cosets_surjective
  simpa [Subgroup.index] using this

theorem sturm_bound_Gamma0_nine {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 9) k)
    (h : ∀ n : ℕ, n ≤ k.toNat → (qExpansion 1 f).coeff n = 0) : f = 0 := by
  refine P2M.sturm_bound_Gamma0 9 f fun n hn ↦ h n ?_
  have hi := Gamma0_nine_index_le
  generalize (CongruenceSubgroup.Gamma0 9).index = m at hn hi
  interval_cases m <;> omega

end KeithZanello.Modular
