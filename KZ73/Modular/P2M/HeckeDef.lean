/-
Ported from the Prove2Me proof repository github.com/anthropics/fermats-last-theorem,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, source files
  Definitions/Def_ModularForm_HeckeOperator.lean
  Definitions/Def_FLTPrelim_Modularity.lean (only the definition `ModularFormClass.qCoeff`).
Apache License 2.0, Copyright 2026 Anthropic, PBC.
Adapted to Lean 4.34.1 and Mathlib v4.34.1: the declarations are moved from the namespaces
`ModularForm` and `ModularFormClass` to `KeithZanello.Modular.P2M`, and the linearity lemmas
that are not used here are omitted.
-/
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The Hecke operator `T_p` on functions on the upper half plane

`heckeT k p f = ∑_{j < p} f ∣[k] !![1, j; 0, p] + f ∣[k] !![p, 0; 0, 1]`, and `coeffHeckeT` is
its expected action on `q`-expansion coefficients.
-/

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace KeithZanello.Modular.P2M

/-- The `n`-th coefficient of the `q`-expansion of period `1`. -/
def qCoeff (f : UpperHalfPlane → ℂ) (n : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff n

def upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

@[simp] theorem val_upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) :
    ((upperTriangularGL a b d had : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![a, b; 0, d] := rfl

def heckeMatrix (p j : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp)

def heckeDiagMatrix (p : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL p 0 1 (by rw [mul_one]; exact_mod_cast hp)

@[simp] theorem val_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) :
    ((heckeMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), (j : ℝ); 0, (p : ℝ)] := by
  simp [heckeMatrix, hp]

@[simp] theorem val_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) :
    ((heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), 0; 0, 1] := by
  simp [heckeDiagMatrix, hp]

@[simp] theorem heckeMatrix_zero (j : ℕ) : heckeMatrix 0 j = 1 := by simp [heckeMatrix]

@[simp] theorem heckeDiagMatrix_zero : heckeDiagMatrix 0 = 1 := by simp [heckeDiagMatrix]

theorem det_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) : ((heckeMatrix p j).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_heckeMatrix hp, Matrix.det_fin_two_of]
  ring

theorem det_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) : ((heckeDiagMatrix p).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_heckeDiagMatrix hp, Matrix.det_fin_two_of]
  ring

theorem det_heckeMatrix_pos (p j : ℕ) : 0 < ((heckeMatrix p j).det : ℝ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [det_heckeMatrix hp]; exact_mod_cast Nat.pos_of_ne_zero hp

theorem det_heckeDiagMatrix_pos (p : ℕ) : 0 < ((heckeDiagMatrix p).det : ℝ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [det_heckeDiagMatrix hp]; exact_mod_cast Nat.pos_of_ne_zero hp

theorem denom_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (heckeMatrix p j) τ = p := by
  simp [UpperHalfPlane.denom, val_heckeMatrix hp]

theorem denom_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (heckeDiagMatrix p) τ = 1 := by
  simp [UpperHalfPlane.denom, val_heckeDiagMatrix hp]

theorem coe_heckeMatrix_smul {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    ((heckeMatrix p j • τ : UpperHalfPlane) : ℂ) = ((τ : ℂ) + j) / p := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_heckeMatrix_pos p j)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_heckeMatrix hp]

theorem coe_heckeDiagMatrix_smul {p : ℕ} (hp : p ≠ 0) (τ : UpperHalfPlane) :
    ((heckeDiagMatrix p • τ : UpperHalfPlane) : ℂ) = (p : ℂ) * (τ : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_heckeDiagMatrix_pos p)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_heckeDiagMatrix hp]

theorem σ_heckeMatrix (p j : ℕ) : UpperHalfPlane.σ (heckeMatrix p j) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, ite_eq_left (det_heckeMatrix_pos p j)]

theorem σ_heckeDiagMatrix (p : ℕ) : UpperHalfPlane.σ (heckeDiagMatrix p) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, ite_eq_left (det_heckeDiagMatrix_pos p)]

theorem slash_heckeMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (j : ℕ) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    (f ∣[k] heckeMatrix p j) τ = (p : ℂ)⁻¹ * f (heckeMatrix p j • τ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [ModularForm.slash_apply, σ_heckeMatrix, det_heckeMatrix hp, denom_heckeMatrix hp]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast]
  rw [mul_assoc, ← zpow_add₀ hp', show k - 1 + -k = -1 by ring, zpow_neg_one, mul_comm]

theorem slash_heckeDiagMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    (f ∣[k] heckeDiagMatrix p) τ = (p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ) := by
  rw [ModularForm.slash_apply, σ_heckeDiagMatrix, det_heckeDiagMatrix hp,
    denom_heckeDiagMatrix hp]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast, one_zpow,
    mul_one]
  rw [mul_comm]

def heckeU (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j

def heckeT (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  heckeU k p f + f ∣[k] heckeDiagMatrix p

theorem heckeU_def (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) :
    heckeU k p f = ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j := rfl

theorem heckeT_eq_heckeU_add (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) :
    heckeT k p f = heckeU k p f + f ∣[k] heckeDiagMatrix p := rfl

@[simp] theorem heckeU_zero_left (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeU k 0 f = 0 := by
  simp [heckeU]

@[simp] theorem heckeT_zero_left (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeT k 0 f = f := by
  simp [heckeT]

theorem heckeU_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    heckeU k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ) := by
  simp only [heckeU, Finset.sum_apply, slash_heckeMatrix_apply k hp, Finset.mul_sum]

theorem heckeT_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    heckeT k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ)
      + (p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ) := by
  rw [heckeT, Pi.add_apply, heckeU_apply k hp, slash_heckeDiagMatrix_apply k hp]

def coeffHeckeT (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0

def coeffHeckeU (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p)

theorem coeffHeckeT_apply (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    coeffHeckeT k p a n = a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0 := rfl

theorem coeffHeckeU_apply (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : coeffHeckeU p a n = a (n * p) := rfl

end KeithZanello.Modular.P2M

end
