import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
import Mathlib.NumberTheory.Modular

/-!
# Linear combinations of translates of `E₂` that are modular forms on `Γ₀(9)`

For `g ∈ GL(2, ℝ)` with integer entries, `E₂ ∣[2] g` is holomorphic and bounded at every cusp
(write `g γ = N⁻¹ U` with `N ∈ SL(2, ℤ)` and `U` upper triangular, then use
`E₂ ∣[2] N⁻¹ = E₂ - c D₂(N⁻¹)`). If moreover each `E₂ ∣[2] gᵢ` transforms like `E₂` under
`Γ₀(9)` (`QuasiE2`), a combination `∑ wᵢ E₂ ∣[2] gᵢ` with `∑ wᵢ = 0` is `Γ₀(9)`-invariant:
`comb` bundles it as a `ModularForm (Γ₀(9)) 2`.

`isBoundedAtImInfty_D2`, `isBoundedAtImInfty_E2_slash_SL` and `isBoundedAtImInfty_E2_slash_of_col`
are adapted from the Prove2Me proof repository github.com/anthropics/fermats-last-theorem,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, source file
  P2M/Sol/S_ModularCurve_isBoundedAtImInfty_eisensteinTwoSlash_slash.lean
(lemmas `isBoundedAtImInfty_D2`, `isBoundedAtImInfty_E2_slash_SL`,
`isBoundedAtImInfty_E2_slash_of_row`, `exists_row_zero`), and `quasiE2_of_conj` follows the
conjugation argument of `P2M/Sol/S_ModularCurve_eisensteinTwoSlash_slash_eq_self.lean`.
Apache License 2.0, Copyright 2026 Anthropic, PBC. Adapted to Lean 4.34.1 and Mathlib v4.34.1:
the diagonal matrix `diag(p, 1)` is replaced by any matrix with integral first column.
-/

open UpperHalfPlane EisensteinSeries Matrix.SpecialLinearGroup OnePoint Complex
open scoped ModularForm MatrixGroups Manifold

namespace KeithZanello.Modular.Eis

noncomputable section

/-- The constant of `E2_slash_action`. -/
def cE : ℂ := 1 / (2 * riemannZeta 2)

/-- `F` transforms like `E₂` under `Γ₀(9)`. -/
def QuasiE2 (F : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 9 → F ∣[(2 : ℤ)] γ = F - cE • D2 γ

/-- `g` has integer entries. -/
def IsIntMat (g : GL (Fin 2) ℝ) : Prop := ∀ i j, ∃ n : ℤ, g i j = n

lemma quasiE2_E2 : QuasiE2 E2 := fun γ _ ↦ E2_slash_action γ

lemma sub_slash' (k : ℤ) (g : GL (Fin 2) ℝ) (f f' : ℍ → ℂ) :
    (f - f') ∣[k] g = f ∣[k] g - f' ∣[k] g := by
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]

/-- A conjugation criterion for `QuasiE2 (E₂ ∣[2] g)`. -/
lemma quasiE2_of_conj (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val)
    (h : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 9 →
      ∃ γ' : SL(2, ℤ), g * mapGL ℝ γ = mapGL ℝ γ' * g ∧ D2 γ' ∣[(2 : ℤ)] g = D2 γ) :
    QuasiE2 (E2 ∣[(2 : ℤ)] g) := by
  intro γ hγ
  obtain ⟨γ', hmul, hD⟩ := h γ hγ
  have hσ : σ g = .refl ℝ ℂ := ite_eq_left_iff.mpr fun h ↦ absurd hg h
  rw [ModularForm.SL_slash, ← SlashAction.slash_mul]
  change E2 ∣[(2 : ℤ)] (g * mapGL ℝ γ) = _
  rw [hmul, SlashAction.slash_mul]
  change (E2 ∣[(2 : ℤ)] γ') ∣[(2 : ℤ)] g = _
  rw [E2_slash_action, sub_slash', ModularForm.smul_slash, hD, hσ]
  rfl

/-! ### Boundedness -/

lemma isBoundedAtImInfty_D2 (γ : SL(2, ℤ)) : IsBoundedAtImInfty (D2 γ) := by
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · have hD : D2 γ = 0 := by
      funext z
      simp [D2, hc]
    rw [hD]
    exact zero_form_isBoundedAtImInfty
  · rw [isBoundedAtImInfty_iff]
    refine ⟨‖2 * (Real.pi : ℂ) * Complex.I * ((γ 1 0 : ℤ) : ℂ)‖, 1, fun z hz ↦ ?_⟩
    have him : (denom γ z).im = ((γ 1 0 : ℤ) : ℝ) * z.im := by
      rw [ModularGroup.denom_apply]
      simp
    have hc1 : (1 : ℝ) ≤ |((γ 1 0 : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs hc
    have hlow : |((γ 1 0 : ℤ) : ℝ)| ≤ ‖denom γ z‖ :=
      calc |((γ 1 0 : ℤ) : ℝ)| = |((γ 1 0 : ℤ) : ℝ)| * 1 := (mul_one _).symm
        _ ≤ |((γ 1 0 : ℤ) : ℝ)| * z.im := by gcongr
        _ = |((γ 1 0 : ℤ) : ℝ) * z.im| := by rw [abs_mul, abs_of_pos z.im_pos]
        _ = |(denom γ z).im| := by rw [him]
        _ ≤ ‖denom γ z‖ := Complex.abs_im_le_norm _
    have hone : (1 : ℝ) ≤ ‖denom γ z‖ := hc1.trans hlow
    change ‖(2 * (Real.pi : ℂ) * Complex.I * ((γ 1 0 : ℤ) : ℂ)) / denom γ z‖ ≤ _
    rw [norm_div]
    exact div_le_self (norm_nonneg _) hone

lemma isBoundedAtImInfty_E2_slash_SL (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (E2 ∣[(2 : ℤ)] γ) := by
  rw [E2_slash_action, sub_eq_add_neg]
  exact isBoundedAtImInfty_E2.add ((isBoundedAtImInfty_D2 γ).smul _).neg

/-- `E₂ ∣[2] g` is bounded at `i∞` when the first column of `g` is integral. -/
lemma isBoundedAtImInfty_E2_slash_of_col (g : GL (Fin 2) ℝ) (a c : ℤ) (ha : g 0 0 = a)
    (hc : g 1 0 = c) : IsBoundedAtImInfty (E2 ∣[(2 : ℤ)] g) := by
  have hentry : ∀ N : SL(2, ℤ), (mapGL ℝ N * g) 1 0 = (N 1 0 : ℝ) * a + (N 1 1 : ℝ) * c := by
    intro N
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ha, hc]
  obtain ⟨N, hN⟩ : ∃ N : SL(2, ℤ), (mapGL ℝ N * g) 1 0 = 0 := by
    rcases eq_or_ne c 0 with h0 | h0
    · exact ⟨1, by rw [hentry]; simp [h0]⟩
    · have hpos : 0 < Int.gcd a c := Int.gcd_pos_of_ne_zero_right a h0
      obtain ⟨a', c', hcop, ha', hc'⟩ := Int.exists_gcd_one hpos
      have hmem : (![-c', a'] : Fin 2 → ℤ) ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} := by
        simpa using (Int.isCoprime_iff_gcd_eq_one.mpr hcop).symm.neg_left
      obtain ⟨N, -, hN⟩ := ModularGroup.bottom_row_surj hmem
      have hN0 : N 1 0 = -c' := by simpa using congrFun hN 0
      have hN1 : N 1 1 = a' := by simpa using congrFun hN 1
      have hz0 : -c' * a + a' * c = 0 := by linear_combination (-c') * ha' + a' * hc'
      refine ⟨N, ?_⟩
      rw [hentry N, hN0, hN1]
      exact_mod_cast hz0
  have h1 : IsBoundedAtImInfty (E2 ∣[(2 : ℤ)] mapGL ℝ N⁻¹) := isBoundedAtImInfty_E2_slash_SL N⁻¹
  have h2 := h1.slash (2 : ℤ) hN
  rwa [← SlashAction.slash_mul, map_inv, inv_mul_cancel_left] at h2

lemma IsIntMat.mul_SL {g : GL (Fin 2) ℝ} (hg : IsIntMat g) (γ : SL(2, ℤ)) :
    IsIntMat (g * mapGL ℝ γ) := by
  intro i j
  obtain ⟨n0, h0⟩ := hg i 0
  obtain ⟨n1, h1⟩ := hg i 1
  refine ⟨n0 * γ 0 j + n1 * γ 1 j, ?_⟩
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h0, h1]

lemma isBoundedAtImInfty_E2_slash_slash {g : GL (Fin 2) ℝ} (hg : IsIntMat g) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty ((E2 ∣[(2 : ℤ)] g) ∣[(2 : ℤ)] γ) := by
  rw [ModularForm.SL_slash, ← SlashAction.slash_mul]
  obtain ⟨a, ha⟩ := hg.mul_SL γ 0 0
  obtain ⟨c, hc⟩ := hg.mul_SL γ 1 0
  exact isBoundedAtImInfty_E2_slash_of_col _ a c ha hc

lemma isBoundedAtImInfty_sum {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, IsBoundedAtImInfty (f i)) : IsBoundedAtImInfty (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero_form_isBoundedAtImInfty : IsBoundedAtImInfty (0 : ℍ → ℂ))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-! ### The combination -/

/-- `∑ᵢ wᵢ • E₂ ∣[2] gᵢ`. -/
def combFun {n : ℕ} (w : Fin n → ℂ) (g : Fin n → GL (Fin 2) ℝ) : ℍ → ℂ :=
  ∑ i, w i • (E2 ∣[(2 : ℤ)] g i)

lemma combFun_apply {n : ℕ} (w : Fin n → ℂ) (g : Fin n → GL (Fin 2) ℝ) (z : ℍ) :
    combFun w g z = ∑ i, w i * (E2 ∣[(2 : ℤ)] g i) z := by
  simp [combFun, Finset.sum_apply]

lemma combFun_slash {n : ℕ} (w : Fin n → ℂ) (g : Fin n → GL (Fin 2) ℝ) (γ : SL(2, ℤ)) :
    combFun w g ∣[(2 : ℤ)] γ = ∑ i, w i • ((E2 ∣[(2 : ℤ)] g i) ∣[(2 : ℤ)] γ) := by
  simp [combFun, SlashAction.sum_slash, ModularForm.SL_smul_slash]

lemma combFun_slash_eq {n : ℕ} (w : Fin n → ℂ) (g : Fin n → GL (Fin 2) ℝ)
    (hq : ∀ i, QuasiE2 (E2 ∣[(2 : ℤ)] g i)) (hw : ∑ i, w i = 0) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 9) : combFun w g ∣[(2 : ℤ)] γ = combFun w g := by
  rw [combFun_slash]
  simp_rw [hq _ γ hγ, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw, zero_smul,
    sub_zero]
  rfl

lemma combFun_holo {n : ℕ} (w : Fin n → ℂ) (g : Fin n → GL (Fin 2) ℝ) :
    MDiff (combFun w g) := by
  unfold combFun
  exact MDifferentiable.sum fun i _ ↦ (E2_mdifferentiable.slash 2 (g i)).const_smul (w i)

lemma combFun_bdd {n : ℕ} (w : Fin n → ℂ) (g : Fin n → GL (Fin 2) ℝ) (hg : ∀ i, IsIntMat (g i))
    (γ : SL(2, ℤ)) : IsBoundedAtImInfty (combFun w g ∣[(2 : ℤ)] γ) := by
  rw [combFun_slash]
  exact isBoundedAtImInfty_sum _ _ fun i _ ↦
    (isBoundedAtImInfty_E2_slash_slash (hg i) γ).smul (w i)

/-- The combination `∑ᵢ wᵢ • E₂ ∣[2] gᵢ` as a modular form of weight 2 on `Γ₀(9)`. -/
def comb {n : ℕ} (w : Fin n → ℂ) (g : Fin n → GL (Fin 2) ℝ) (hg : ∀ i, IsIntMat (g i))
    (hq : ∀ i, QuasiE2 (E2 ∣[(2 : ℤ)] g i)) (hw : ∑ i, w i = 0) :
    ModularForm (CongruenceSubgroup.Gamma0 9) 2 where
  toFun := combFun w g
  slash_action_eq' γ hγ := by
    obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.mp hγ
    exact combFun_slash_eq w g hq hw γ₀ hγ₀
  holo' := combFun_holo w g
  bdd_at_cusps' {c} hc := by
    have hc' : IsCusp c 𝒮ℒ := hc.mono (Subgroup.map_le_range _ _)
    rw [isBoundedAt_iff_forall_SL2Z hc']
    intro γ _
    exact combFun_bdd w g hg γ

lemma coe_comb {n : ℕ} (w : Fin n → ℂ) (g : Fin n → GL (Fin 2) ℝ) (hg : ∀ i, IsIntMat (g i))
    (hq : ∀ i, QuasiE2 (E2 ∣[(2 : ℤ)] g i)) (hw : ∑ i, w i = 0) :
    ⇑(comb w g hg hq hw) = combFun w g := rfl

end

end KeithZanello.Modular.Eis
