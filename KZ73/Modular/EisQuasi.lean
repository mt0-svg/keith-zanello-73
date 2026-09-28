import KZ73.Modular.EisBasic

/-!
# The translates `E₂ ∣[2] diag(3, 1)` and `E₂ ∣[2] [[3, u], [0, 3]]` transform like `E₂` on `Γ₀(9)`

* `α3 = diag(3, 1)`: `E₂ ∣[2] α3 (z) = 3 E₂(3z)`; for `γ = [[a, b], [c, d]] ∈ Γ₀(9)`,
  `α3 γ = γ' α3` with `γ' = [[a, 3b], [c/3, d]]` and `D₂(γ') ∣[2] α3 = D₂(γ)`.
* `A u = [[3, u], [0, 3]]`: `E₂ ∣[2] A u (z) = E₂(z + u/3)`; for `γ ∈ Γ₀(9)` (so `9 ∣ c` and
  `3 ∣ d - a`), `A u γ = γ_u (A u)` with
  `γ_u = [[a + u c/3, b + u (d - a)/3 - u² c/9], [c, d - u c/3]]` and `D₂(γ_u) ∣[2] A u = D₂(γ)`.
-/

open UpperHalfPlane EisensteinSeries Matrix.SpecialLinearGroup Complex
open scoped ModularForm MatrixGroups

namespace KeithZanello.Modular.Eis

noncomputable section

/-- The integer matrix `!![a, b; c, d]` (nonzero determinant) in `GL(2, ℝ)`. -/
def glZ (a b c d : ℤ) (h : a * d - b * c ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(a : ℝ), b; c, d]
    (by rw [Matrix.det_fin_two_of]; exact_mod_cast h)

lemma coe_glZ (a b c d : ℤ) (h : a * d - b * c ≠ 0) :
    (glZ a b c d h : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; c, d] := rfl

lemma det_glZ (a b c d : ℤ) (h : a * d - b * c ≠ 0) :
    (glZ a b c d h).det.val = a * d - b * c := by
  simp [Matrix.GeneralLinearGroup.val_det_apply, coe_glZ, Matrix.det_fin_two_of]

lemma isIntMat_glZ (a b c d : ℤ) (h : a * d - b * c ≠ 0) : IsIntMat (glZ a b c d h) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨a, by simp [coe_glZ]⟩
  · exact ⟨b, by simp [coe_glZ]⟩
  · exact ⟨c, by simp [coe_glZ]⟩
  · exact ⟨d, by simp [coe_glZ]⟩

lemma glZ_upper_smul (a b d : ℤ) (h : a * d - b * 0 ≠ 0) (hpos : 0 < a * d) (z : ℍ) :
    ((glZ a b 0 d h • z : ℍ) : ℂ) = (a * z + b) / d := by
  have hdet : 0 < (glZ a b 0 d h).det.val := by
    rw [det_glZ]; simpa using (by exact_mod_cast hpos : (0 : ℝ) < a * d)
  rw [coe_smul_of_det_pos hdet]
  simp [num, denom, coe_glZ]

lemma slash_glZ_upper_apply (f : ℍ → ℂ) (a b d : ℤ) (h : a * d - b * 0 ≠ 0) (hpos : 0 < a * d)
    (z : ℍ) : (f ∣[(2 : ℤ)] glZ a b 0 d h) z = (a / d : ℂ) * f (glZ a b 0 d h • z) := by
  have hdet : 0 < (glZ a b 0 d h).det.val := by
    rw [det_glZ]; simpa using (by exact_mod_cast hpos : (0 : ℝ) < a * d)
  have hσ : σ (glZ a b 0 d h) = .refl ℝ ℂ := ite_eq_left_iff.mpr fun h ↦ absurd hdet h
  have hd : (d : ℂ) ≠ 0 := by
    have : d ≠ 0 := by rintro rfl; simp at hpos
    exact_mod_cast this
  rw [ModularForm.slash_apply, hσ, abs_of_pos hdet, det_glZ]
  simp only [ContinuousAlgEquiv.refl_apply, denom, coe_glZ]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Int.cast_zero, zero_mul,
    Complex.ofReal_zero, zero_add, Complex.ofReal_intCast, mul_zero, sub_zero]
  push_cast
  field_simp

/-! ### `α3 = diag(3, 1)` -/

/-- `diag(3, 1)`. -/
def α3 : GL (Fin 2) ℝ := glZ 3 0 0 1 (by norm_num)

lemma α3_smul (z : ℍ) : ((α3 • z : ℍ) : ℂ) = 3 * z := by
  rw [α3, glZ_upper_smul _ _ _ _ (by norm_num)]
  simp

lemma slash_α3_apply (f : ℍ → ℂ) (z : ℍ) : (f ∣[(2 : ℤ)] α3) z = 3 * f (α3 • z) := by
  rw [α3, slash_glZ_upper_apply _ _ _ _ _ (by norm_num)]
  norm_num

lemma dvd_nine_of_mem {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 9) :
    (9 : ℤ) ∣ γ 1 0 := by
  have := CongruenceSubgroup.Gamma0_mem.mp hγ
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mp this

lemma dvd_three_sub_of_mem {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 9) :
    (3 : ℤ) ∣ γ 1 1 - γ 0 0 := by
  obtain ⟨c, hc⟩ := dvd_nine_of_mem hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  have h3 : ((γ 0 0 : ℤ) : ZMod 3) * ((γ 1 1 : ℤ) : ZMod 3) = 1 := by
    have : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod 3) = 1 := by rw [hdet]; simp
    rw [hc] at this
    push_cast at this
    have h9 : ((9 : ℤ) : ZMod 3) = 0 := by decide
    push_cast at h9
    rw [h9] at this
    simpa using this
  have key : ∀ x y : ZMod 3, x * y = 1 → y - x = 0 := by decide
  have := key _ _ h3
  rw [← Int.cast_sub] at this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp this

/-- `[[a, 3b], [c/3, d]]` for `γ ∈ Γ₀(9)`. -/
def conj3 (γ : SL(2, ℤ)) (c' : ℤ) (hc : γ 1 0 = 3 * c') : SL(2, ℤ) :=
  ⟨!![γ 0 0, 3 * γ 0 1; c', γ 1 1], by
    have hdet := γ.det_coe
    rw [Matrix.det_fin_two, hc] at hdet
    rw [Matrix.det_fin_two_of]
    linarith⟩

-- The option below restores the older elaborator behaviour in which `isDefEq` may unfold
-- definitions regardless of the requested transparency. It affects elaboration only: the kernel
-- still checks the resulting proof term.
set_option backward.isDefEq.respectTransparency false in
lemma α3_mul (γ : SL(2, ℤ)) (c' : ℤ) (hc : γ 1 0 = 3 * c') :
    α3 * mapGL ℝ γ = mapGL ℝ (conj3 γ c' hc) * α3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [α3, coe_glZ, conj3, Matrix.mul_apply, Fin.sum_univ_two, hc] <;> ring

lemma D2_conj3_slash (γ : SL(2, ℤ)) (c' : ℤ) (hc : γ 1 0 = 3 * c') :
    D2 (conj3 γ c' hc) ∣[(2 : ℤ)] α3 = D2 γ := by
  ext z
  rw [slash_α3_apply]
  simp only [D2, ModularGroup.denom_apply]
  rw [α3_smul]
  have hden : ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) z
    rwa [ModularGroup.denom_apply] at this
  simp only [conj3, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at hden ⊢
  rw [hc] at hden ⊢
  push_cast at hden ⊢
  have hden' : (c' : ℂ) * (3 * (z : ℂ)) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    convert hden using 1; ring
  field_simp

lemma quasiE2_α3 : QuasiE2 (E2 ∣[(2 : ℤ)] α3) := by
  refine quasiE2_of_conj α3 (by rw [α3, det_glZ]; norm_num) fun γ hγ ↦ ?_
  obtain ⟨c, hc⟩ := dvd_nine_of_mem hγ
  have hc3 : γ 1 0 = 3 * (3 * c) := by rw [hc]; ring
  exact ⟨conj3 γ (3 * c) hc3, α3_mul γ _ hc3, D2_conj3_slash γ _ hc3⟩

/-! ### `A u = [[3, u], [0, 3]]` -/

/-- `[[3, u], [0, 3]]`. -/
def A (u : ℤ) : GL (Fin 2) ℝ := glZ 3 u 0 3 (by norm_num)

lemma A_smul (u : ℤ) (z : ℍ) : ((A u • z : ℍ) : ℂ) = z + u / 3 := by
  rw [A, glZ_upper_smul _ _ _ _ (by norm_num)]
  push_cast
  ring

lemma slash_A_apply (f : ℍ → ℂ) (u : ℤ) (z : ℍ) : (f ∣[(2 : ℤ)] A u) z = f (A u • z) := by
  rw [A, slash_glZ_upper_apply _ _ _ _ _ (by norm_num)]
  norm_num

/-- `γ_u = [[a + 3 u c', b + u e - u² c'], [9 c', d - 3 u c']]` for `c = 9 c'`, `d - a = 3 e`. -/
def conjA (γ : SL(2, ℤ)) (u c' e : ℤ) (hc : γ 1 0 = 9 * c') (he : γ 1 1 - γ 0 0 = 3 * e) :
    SL(2, ℤ) :=
  ⟨!![γ 0 0 + 3 * u * c', γ 0 1 + u * e - u ^ 2 * c'; 9 * c', γ 1 1 - 3 * u * c'], by
    have hdet := γ.det_coe
    rw [Matrix.det_fin_two, hc] at hdet
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + 3 * u * c' * he⟩

-- Same elaborator-only option as for `α3_mul`.
set_option backward.isDefEq.respectTransparency false in
lemma A_mul (γ : SL(2, ℤ)) (u c' e : ℤ) (hc : γ 1 0 = 9 * c') (he : γ 1 1 - γ 0 0 = 3 * e) :
    A u * mapGL ℝ γ = mapGL ℝ (conjA γ u c' e hc he) * A u := by
  have he' : (γ 1 1 : ℝ) = γ 0 0 + 3 * e := by
    have : γ 1 1 = γ 0 0 + 3 * e := by linarith
    exact_mod_cast this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, coe_glZ, conjA, Matrix.mul_apply, Fin.sum_univ_two, hc, he'] <;> ring

lemma D2_conjA_slash (γ : SL(2, ℤ)) (u c' e : ℤ) (hc : γ 1 0 = 9 * c')
    (he : γ 1 1 - γ 0 0 = 3 * e) : D2 (conjA γ u c' e hc he) ∣[(2 : ℤ)] A u = D2 γ := by
  ext z
  rw [slash_A_apply]
  simp only [D2, ModularGroup.denom_apply]
  rw [A_smul]
  simp only [conjA, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [hc]
  push_cast
  congr 1
  ring

lemma quasiE2_A (u : ℤ) : QuasiE2 (E2 ∣[(2 : ℤ)] A u) := by
  refine quasiE2_of_conj (A u) (by rw [A, det_glZ]; norm_num) fun γ hγ ↦ ?_
  obtain ⟨c, hc⟩ := dvd_nine_of_mem hγ
  obtain ⟨e, he⟩ := dvd_three_sub_of_mem hγ
  exact ⟨conjA γ u c e hc he, A_mul γ u c e hc he, D2_conjA_slash γ u c e hc he⟩

end

end KeithZanello.Modular.Eis
