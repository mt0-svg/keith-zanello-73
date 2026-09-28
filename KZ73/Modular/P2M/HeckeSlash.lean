/-
Ported from the Prove2Me proof repository github.com/anthropics/fermats-last-theorem,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, source file
  P2M/Sol/S_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0.lean
(statement in Theorems/Thm_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0.lean).
Apache License 2.0, Copyright 2026 Anthropic, PBC.
Adapted to Lean 4.34.1 and Mathlib v4.34.1: the `p2m_*` commands are removed, the results are
stated in the namespace `KeithZanello.Modular.P2M`, and the `U_p` variant (for `p ∣ N`) is
omitted.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import KZ73.Modular.P2M.HeckeDef

/-!
# `T_p` preserves invariance under `Γ₀(N)` for `p ∤ N`

The matrices defining `T_p` are indexed by `P¹(𝔽_p)`, and right multiplication by
`γ ∈ Γ₀(N)` permutes them modulo `Γ₀(N)` on the left.
-/

set_option autoImplicit false

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm OnePoint

namespace KeithZanello.Modular.P2M

namespace HeckeSlashInvariance
@[scoped simp] theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

/-- An element of `SL(2, ℤ)` given by a matrix; unlike the anonymous constructor, the term has
type `SL(2, ℤ)` at reducible transparency, so `simp` can rewrite its entries. -/
def mkSL2 (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M.det = 1) : SL(2, ℤ) := ⟨M, h⟩

@[scoped simp] theorem coe_mkSL2 (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M.det = 1) :
    ((mkSL2 M h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = M := rfl

theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

section commutation

variable {p : ℕ} (hp : p ≠ 0)
include hp

theorem heckeMatrix_mul_of_eq (g : SL(2, ℤ)) (j j' : ℕ) (e : ℤ)
    (he : g 0 1 + j * g 1 1 = j' * (g 0 0 + j * g 1 0) + p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = p * g 1 0 ∧
      heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j' := by
  have hdet := det_eq g
  refine ⟨mkSL2 !![g 0 0 + j * g 1 0, e; p * g 1 0, g 1 1 - g 1 0 * j'] ?_, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 1 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

theorem heckeMatrix_mul_of_eq' (g : SL(2, ℤ)) (j : ℕ) (e : ℤ)
    (he : g 0 0 + j * g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧
      heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨mkSL2 !![e, g 0 1 + j * g 1 1; g 1 0, p * g 1 1] ?_, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 1 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

theorem heckeDiagMatrix_mul_of_eq (g : SL(2, ℤ)) (j' : ℕ) (e : ℤ)
    (he : g 1 1 = g 1 0 * j' + p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧
      heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j' := by
  have hdet := det_eq g
  refine ⟨mkSL2 !![p * g 0 0, g 0 1 - g 0 0 * j'; g 1 0, e] ?_, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 0 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

theorem heckeDiagMatrix_mul_of_eq' (g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = e ∧
      heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨mkSL2 !![g 0 0, p * g 0 1; e, g 1 1] ?_, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 0 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

end commutation

section reindex

variable {p : ℕ} [NeZero p]

theorem sum_range_eq_sum_zmod {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ j ∈ Finset.range p, F j = ∑ x : ZMod p, F x.val := by
  refine Finset.sum_nbij' (fun j : ℕ ↦ (j : ZMod p)) (fun x : ZMod p ↦ x.val) (fun _ _ ↦ Finset.mem_univ _)
    (fun x _ ↦ Finset.mem_range.mpr x.val_lt) (fun j hj ↦ ?_) (fun x _ ↦ ?_) (fun j hj ↦ ?_)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · exact ZMod.natCast_zmod_val x
  · rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]

theorem heckeU_eq_sum_zmod (k : ℤ) (f : ℍ → ℂ) :
    heckeU k p f = ∑ x : ZMod p, f ∣[k] heckeMatrix p x.val := by
  rw [heckeU_def]
  exact sum_range_eq_sum_zmod _

end reindex


section heckeT

variable {p : ℕ}

def heckeRep (p : ℕ) (x : OnePoint (ZMod p)) : GL (Fin 2) ℝ :=
  x.elim (heckeDiagMatrix p) (fun j ↦ heckeMatrix p j.val)

@[scoped simp] theorem heckeRep_infty : heckeRep p ∞ = heckeDiagMatrix p := rfl

@[scoped simp] theorem heckeRep_coe (j : ZMod p) : heckeRep p j = heckeMatrix p j.val := rfl

theorem heckeT_eq_sum_onePoint [NeZero p] (k : ℤ) (f : ℍ → ℂ) :
    heckeT k p f = ∑ x : OnePoint (ZMod p), f ∣[k] heckeRep p x := by
  rw [heckeT_eq_heckeU_add, heckeU_eq_sum_zmod, add_comm]
  exact (Fintype.sum_option (fun x : OnePoint (ZMod p) ↦ f ∣[k] heckeRep p x)).symm

variable [Fact p.Prime]

variable (p) in

def redMatrix (g : SL(2, ℤ)) : GL (Fin 2) (ZMod p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((g 1 1 : ℤ) : ZMod p), ((g 0 1 : ℤ) : ZMod p); ((g 1 0 : ℤ) : ZMod p), ((g 0 0 : ℤ) : ZMod p)]
    (by
      have := congrArg (Int.cast : ℤ → ZMod p) (det_eq g)
      push_cast at this
      rw [Matrix.det_fin_two_of,
        show ((g 1 1 : ℤ) : ZMod p) * ((g 0 0 : ℤ) : ZMod p) - ((g 0 1 : ℤ) : ZMod p) * ((g 1 0 : ℤ) : ZMod p)
          = 1 by linear_combination this]
      exact one_ne_zero)

@[scoped simp] theorem redMatrix_apply_zero_zero (g : SL(2, ℤ)) :
    redMatrix p g 0 0 = ((g 1 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[scoped simp] theorem redMatrix_apply_zero_one (g : SL(2, ℤ)) :
    redMatrix p g 0 1 = ((g 0 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[scoped simp] theorem redMatrix_apply_one_zero (g : SL(2, ℤ)) :
    redMatrix p g 1 0 = ((g 1 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[scoped simp] theorem redMatrix_apply_one_one (g : SL(2, ℤ)) :
    redMatrix p g 1 1 = ((g 0 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

scoped instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

theorem heckeRep_mul {N : ℕ} (hpN : ¬ p ∣ N) (g : SL(2, ℤ)) (hg : (N : ℤ) ∣ g 1 0)
    (x : OnePoint (ZMod p)) :
    ∃ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 ∧
      heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : ((g 1 0 : ℤ) : ZMod p) = 0
    ·
      rw [ite_eq_left (by simpa using hc), heckeRep_infty]
      obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
      obtain ⟨g', hg', hmul⟩ := heckeDiagMatrix_mul_of_eq' hp g e he
      refine ⟨g', ?_, hmul⟩
      rw [hg']
      have hcop : IsCoprime (N : ℤ) (p : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN).symm
      exact hcop.dvd_of_dvd_mul_left (he ▸ hg)
    ·
      rw [ite_eq_right (by simpa using hc), heckeRep_infty, heckeRep_coe]
      set y : ZMod p := redMatrix p g 0 0 / redMatrix p g 1 0
        with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 1 1 - g 1 0 * y.val := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, hy, redMatrix_apply_zero_zero, redMatrix_apply_one_zero,
          mul_div_cancel₀ _ hc, sub_self]
      obtain ⟨g', hg', hmul⟩ := heckeDiagMatrix_mul_of_eq hp g y.val e (by linear_combination he)
      exact ⟨g', hg' ▸ hg, hmul⟩
  | coe j =>
    rw [OnePoint.smul_some_eq_ite]
    by_cases h : redMatrix p g 1 0 * j + redMatrix p g 1 1 = 0
    ·
      rw [ite_eq_left h, heckeRep_infty, heckeRep_coe]
      rw [redMatrix_apply_one_zero, redMatrix_apply_one_one] at h
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 0 + j.val * g 1 0 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val]
        linear_combination h
      obtain ⟨g', hg', hmul⟩ := heckeMatrix_mul_of_eq' hp g j.val e he
      exact ⟨g', hg' ▸ hg, hmul⟩
    ·
      rw [ite_eq_right h, heckeRep_coe, heckeRep_coe]
      set y : ZMod p := (redMatrix p g 0 0 * j + redMatrix p g 0 1) /
        (redMatrix p g 1 0 * j + redMatrix p g 1 1) with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 1 + j.val * g 1 1 - y.val * (g 0 0 + j.val * g 1 0) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
          show ((g 0 0 : ℤ) : ZMod p) + j * ((g 1 0 : ℤ) : ZMod p)
            = redMatrix p g 1 0 * j + redMatrix p g 1 1 by
              rw [redMatrix_apply_one_zero, redMatrix_apply_one_one]; ring,
          hy, div_mul_cancel₀ _ h, redMatrix_apply_zero_zero, redMatrix_apply_zero_one]
        ring
      obtain ⟨g', hg', hmul⟩ := heckeMatrix_mul_of_eq hp g j.val y.val e (by linear_combination he)
      exact ⟨g', hg' ▸ dvd_mul_of_dvd_right hg _, hmul⟩

variable {N : ℕ} (k : ℤ)

theorem heckeT_slash_mapGL (hpN : ¬ p ∣ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    heckeT k p f ∣[k] (mapGL ℝ g) = heckeT k p f := by
  have hcN : (N : ℤ) ∣ g 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hg)
  rw [heckeT_eq_sum_onePoint k f, SlashAction.sum_slash]
  calc ∑ x : OnePoint (ZMod p), (f ∣[k] heckeRep p x) ∣[k] mapGL ℝ g
      = ∑ x : OnePoint (ZMod p), f ∣[k] heckeRep p (redMatrix p g • x) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        obtain ⟨g', hg', hmul⟩ := heckeRep_mul hpN g hcN x
        have hg'N : g' ∈ CongruenceSubgroup.Gamma0 N :=
          CongruenceSubgroup.Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hg')
        rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul,
          hf _ (Subgroup.mem_map_of_mem (mapGL ℝ) hg'N)]
    _ = ∑ x : OnePoint (ZMod p), f ∣[k] heckeRep p x :=
        Equiv.sum_comp (MulAction.toPerm (redMatrix p g)) (fun x ↦ f ∣[k] heckeRep p x)

end heckeT

end HeckeSlashInvariance

open HeckeSlashInvariance in
/-- For `p ∤ N` prime, `T_p` maps `Γ₀(N)`-invariant functions to `Γ₀(N)`-invariant functions. -/
theorem heckeT_slash_eq_self_of_mem_Gamma0 {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map k γ f = f)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    SlashAction.map k γ (heckeT k p f) = heckeT k p f := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, rfl⟩ := hγ
  exact heckeT_slash_mapGL k hpN f hf g hg

end KeithZanello.Modular.P2M

end
