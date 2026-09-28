/-
Ported from the Prove2Me proof repository github.com/anthropics/fermats-last-theorem,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, source file
  P2M/Sol/S_CuspFormClass_isZeroAt_heckeT.lean
(statement in Theorems/Thm_CuspFormClass_isZeroAt_heckeT.lean).
Apache License 2.0, Copyright 2026 Anthropic, PBC.
Adapted to Lean 4.34.1 and Mathlib v4.34.1: the `p2m_*` commands are removed, the results are
stated in the namespace `KeithZanello.Modular.P2M`, and only the boundedness half is kept (the
vanishing half for cusp forms is omitted).
-/
import Mathlib.NumberTheory.ModularForms.Basic
import KZ73.Modular.P2M.HeckeDef

/-!
# `T_p f` is bounded at every cusp

The matrices defining `T_p` have rational entries, so they permute the cusps of an arithmetic
subgroup, and `T_p f` is bounded at every cusp when `f` is a modular form.
-/

set_option autoImplicit false

noncomputable section

open UpperHalfPlane OnePoint
open scoped MatrixGroups ModularForm

namespace KeithZanello.Modular.P2M

section RatCusps

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}

theorem isCusp_ratCast_smul {c : OnePoint ℝ} (hc : IsCusp c Γ) (g : GL (Fin 2) ℚ) :
    IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) Γ := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  exact ⟨g • c, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

theorem isBoundedAt_slash_ratCast [ModularFormClass F Γ k] (f : F) (g : GL (Fin 2) ℚ)
    {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsBoundedAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k :=
  OnePoint.IsBoundedAt.smul_iff.mp (ModularFormClass.bdd_at_cusps f (isCusp_ratCast_smul hc g))

end RatCusps

section HeckeMatrices

def ratUpperTriangularGL (a b d : ℚ) (had : a * d ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

theorem exists_heckeMatrix_eq_map (p j : ℕ) :
    ∃ g : GL (Fin 2) ℚ, heckeMatrix p j = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by rw [heckeMatrix_zero, map_one]⟩
  · refine ⟨ratUpperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heckeMatrix, hp, ratUpperTriangularGL, upperTriangularGL,
        Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem exists_heckeDiagMatrix_eq_map (p : ℕ) :
    ∃ g : GL (Fin 2) ℚ, heckeDiagMatrix p = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by rw [heckeDiagMatrix_zero, map_one]⟩
  · refine ⟨ratUpperTriangularGL p 0 1 (by rw [mul_one]; exact_mod_cast hp), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heckeDiagMatrix, hp, ratUpperTriangularGL, upperTriangularGL,
        Matrix.GeneralLinearGroup.mkOfDetNeZero]

end HeckeMatrices

section Cusps

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}

theorem isBoundedAt_sum {ι : Type*} {c : OnePoint ℝ} {k : ℤ} (s : Finset ι)
    {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, c.IsBoundedAt (f i) k) :
    c.IsBoundedAt (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    rw [Finset.sum_empty, SlashAction.zero_slash]
    exact Filter.const_boundedAtFilter _ (0 : ℂ)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem isBoundedAt_heckeU [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ}
    (hc : IsCusp c Γ) : c.IsBoundedAt (heckeU k p ⇑f) k := by
  rw [heckeU_def]
  refine isBoundedAt_sum _ fun j _ => ?_
  obtain ⟨g, hg⟩ := exists_heckeMatrix_eq_map p j
  rw [hg]
  exact isBoundedAt_slash_ratCast f g hc

/-- `T_p f` is bounded at every cusp of `Γ` when `f` is a modular form on `Γ`. -/
theorem isBoundedAt_heckeT [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ}
    (hc : IsCusp c Γ) : c.IsBoundedAt (heckeT k p ⇑f) k := by
  rw [heckeT_eq_heckeU_add]
  refine (isBoundedAt_heckeU f p hc).add ?_
  obtain ⟨g, hg⟩ := exists_heckeDiagMatrix_eq_map p
  rw [hg]
  exact isBoundedAt_slash_ratCast f g hc

end Cusps

end KeithZanello.Modular.P2M

end
