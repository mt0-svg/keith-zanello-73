import KZ73.Modular.Coeffs
import KZ73.Modular.EisQuasi
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Three weight 2 modular forms on `Γ₀(9)` built from `E₂`

* `H₀ = (3 E₂(3z) - E₂(z)) / 2 = (E₂ ∣[2] diag(3,1) - E₂) / 2`;
* `M_r = -(1/72) ∑_{u = 0}^{2} ω^{-r u} E₂(z + u/3)` for `r = 1, 2`, `ω = e^{2πi/3}`,
  whose `q`-expansion is `∑_{n ≡ r (3)} σ₁(n) qⁿ`.

Invariance under `Γ₀(9)`: for `γ ∈ Γ₀(9)`, `E₂ ∣[2] γ = E₂ - c D₂(γ)` (Mathlib's `E2_slash_action`);
the `D₂` terms cancel in `H₀` (conjugation by `diag(3,1)`) and in `M_r` (conjugation by
`z ↦ z + u/3` fixes `D₂(γ)` because `9 ∣ γ₁₀` and `γ₀₀ ≡ γ₁₁ (mod 3)`, and `∑_u ω^{-r u} = 0`).
The forms are built by `Eis.comb` (`EisBasic.lean`) from the transformation laws of
`EisQuasi.lean`; the coefficients come from `hasSum_qExpansion_E2` and
`ModularFormClass.qExpansion_coeff_unique`.
-/

open UpperHalfPlane

namespace KeithZanello.Modular

namespace Eis

open EisensteinSeries Complex
open scoped ModularForm MatrixGroups ArithmeticFunction.sigma

noncomputable section

/-- The `q`-expansion coefficients of `E₂`. -/
def e2c (m : ℕ) : ℂ := if m = 0 then 1 else -24 * σ 1 m

lemma hasSum_E2 (z : ℍ) :
    HasSum (fun m : ℕ ↦ e2c m * cexp (2 * Real.pi * Complex.I * z) ^ m) (E2 z) := by
  simpa [e2c, smul_eq_mul] using hasSum_qExpansion_E2 (z := z)

lemma qParam_one (z : ℍ) : Function.Periodic.qParam 1 (z : ℂ) = cexp (2 * Real.pi * Complex.I * z) := by
  simp [Function.Periodic.qParam]

lemma one_mem_strictPeriods :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 9 : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

/-- Coefficients from a `q`-expansion identity. -/
lemma coeff_eq_of_hasSum (f : ModularForm (CongruenceSubgroup.Gamma0 9) 2) (c : ℕ → ℂ)
    (hf : ∀ z : ℍ, HasSum (fun m : ℕ ↦ c m * cexp (2 * Real.pi * Complex.I * z) ^ m) (f z)) (n : ℕ) :
    (qExpansion 1 f).coeff n = c n := by
  refine (ModularFormClass.qExpansion_coeff_unique (h := 1) one_pos one_mem_strictPeriods
    (fun z ↦ ?_) n).symm
  simpa [qParam_one, smul_eq_mul] using hf z

/-! ### `H₀` -/

lemma isIntMat_one : IsIntMat 1 := by
  intro i j
  refine ⟨if i = j then 1 else 0, ?_⟩
  by_cases h : i = j <;> simp [h]

lemma quasiE2_one : QuasiE2 (E2 ∣[(2 : ℤ)] (1 : GL (Fin 2) ℝ)) := by
  rw [SlashAction.slash_one]
  exact quasiE2_E2

/-- `H₀ = (1/2) E₂ ∣[2] diag(3,1) - (1/2) E₂`. -/
def H0 : ModularForm (CongruenceSubgroup.Gamma0 9) 2 :=
  comb ![1 / 2, -1 / 2] ![α3, 1]
    (by
      intro i
      fin_cases i
      · exact isIntMat_glZ 3 0 0 1 (by norm_num)
      · exact isIntMat_one)
    (by
      intro i
      fin_cases i
      · exact quasiE2_α3
      · exact quasiE2_one)
    (by simp [Fin.sum_univ_two]; norm_num)

lemma H0_apply (z : ℍ) : H0 z = 3 / 2 * E2 (α3 • z) - 1 / 2 * E2 z := by
  change combFun _ _ z = _
  rw [combFun_apply]
  simp [Fin.sum_univ_two, slash_α3_apply]
  ring

lemma hasSum_E2_α3 (z : ℍ) :
    HasSum (fun n : ℕ ↦ (if 3 ∣ n then e2c (n / 3) else 0) * cexp (2 * Real.pi * Complex.I * z) ^ n)
      (E2 (α3 • z)) := by
  have h := hasSum_E2 (α3 • z)
  have hq : cexp (2 * Real.pi * Complex.I * ((α3 • z : ℍ) : ℂ)) = cexp (2 * Real.pi * Complex.I * z) ^ 3 := by
    rw [α3_smul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hq] at h
  have hinj : Function.Injective (fun m : ℕ ↦ 3 * m) := fun a b hab ↦ by simpa using hab
  refine (hinj.hasSum_iff (fun n hn ↦ ?_)).mp ?_
  · have h3 : ¬ 3 ∣ n := by
      rintro ⟨m, rfl⟩
      exact hn ⟨m, rfl⟩
    simp [h3]
  · convert h using 1
    funext m
    simp [pow_mul]

lemma h0Coeff_eq (n : ℕ) :
    (h0Coeff n : ℂ) = 3 / 2 * (if 3 ∣ n then e2c (n / 3) else 0) - 1 / 2 * e2c n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [h0Coeff, e2c]
    norm_num
  · have hn0 : n ≠ 0 := hn.ne'
    by_cases h3 : 3 ∣ n
    · have hd : n / 3 ≠ 0 := by
        obtain ⟨m, rfl⟩ := h3
        omega
      simp [h0Coeff, e2c, hn0, h3, hd]
      ring
    · simp [h0Coeff, e2c, hn0, h3]
      ring

lemma hasSum_H0 (z : ℍ) :
    HasSum (fun n : ℕ ↦ (h0Coeff n : ℂ) * cexp (2 * Real.pi * Complex.I * z) ^ n) (H0 z) := by
  rw [H0_apply]
  convert ((hasSum_E2_α3 z).mul_left (3 / 2)).sub ((hasSum_E2 z).mul_left (1 / 2)) using 1
  funext n
  rw [h0Coeff_eq]
  ring

/-! ### `M₁`, `M₂` -/

/-- `ω = e^{2πi/3}`. -/
def ω : ℂ := cexp (2 * Real.pi * Complex.I / 3)

lemma ω_prim : IsPrimitiveRoot ω 3 := by
  simpa [ω] using Complex.isPrimitiveRoot_exp 3 (by norm_num)

lemma ω_pow_three : ω ^ 3 = 1 := ω_prim.pow_eq_one

lemma ω_pow_mod (n : ℕ) : ω ^ n = ω ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, ω_pow_three, one_pow, mul_one]

lemma one_add_ω_add_ω_sq : 1 + ω + ω ^ 2 = 0 := by
  have := ω_prim.geom_sum_eq_zero (by norm_num : 1 < 3)
  simpa [Finset.sum_range_succ, add_assoc] using this

/-- `∑_{u < 3} ω^{k u} = 3 [3 ∣ k]`. -/
lemma sum_ω_pow (k : ℕ) : ∑ u : Fin 3, ω ^ (k * (u : ℕ)) = if 3 ∣ k then 3 else 0 := by
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, pow_zero, mul_one]
  rw [ω_pow_mod k, ω_pow_mod (k * 2)]
  have hk : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have h2 : k * 2 % 3 = (k % 3) * 2 % 3 := by omega
  rw [h2]
  interval_cases hr : k % 3
  · simp [Nat.dvd_iff_mod_eq_zero, hr]
    norm_num
  · have : ¬ 3 ∣ k := by omega
    simp only [this, ite_false]
    norm_num
    linear_combination one_add_ω_add_ω_sq
  · have : ¬ 3 ∣ k := by omega
    simp only [this, ite_false]
    norm_num
    linear_combination one_add_ω_add_ω_sq

/-- Weights of `M_r`: `-(1/72) ω^{j u}` with `j ≡ -r (mod 3)`. -/
def wM (j : ℕ) (u : Fin 3) : ℂ := -(1 / 72) * ω ^ (j * (u : ℕ))

lemma sum_wM {j : ℕ} (hj : ¬ 3 ∣ j) : ∑ u, wM j u = 0 := by
  simp only [wM, ← Finset.mul_sum, sum_ω_pow, hj, ite_false, mul_zero]

/-- `M = -(1/72) ∑_{u < 3} ω^{j u} E₂ ∣[2] [[3, u], [0, 3]]`. -/
def Mj (j : ℕ) (hj : ¬ 3 ∣ j) : ModularForm (CongruenceSubgroup.Gamma0 9) 2 :=
  comb (wM j) (fun u ↦ A (u : ℕ)) (fun u ↦ isIntMat_glZ 3 (u : ℕ) 0 3 (by norm_num)) (fun _ ↦ quasiE2_A _)
    (sum_wM hj)

lemma Mj_apply (j : ℕ) (hj : ¬ 3 ∣ j) (z : ℍ) :
    Mj j hj z = ∑ u : Fin 3, wM j u * E2 (A (u : ℕ) • z) := by
  change combFun _ _ z = _
  rw [combFun_apply]
  simp [slash_A_apply]

lemma hasSum_E2_A (u : ℕ) (z : ℍ) :
    HasSum (fun m : ℕ ↦ e2c m * ω ^ (u * m) * cexp (2 * Real.pi * Complex.I * z) ^ m)
      (E2 (A u • z)) := by
  have h := hasSum_E2 (A u • z)
  have hq : cexp (2 * Real.pi * Complex.I * ((A u • z : ℍ) : ℂ)) =
      cexp (2 * Real.pi * Complex.I * z) * ω ^ u := by
    rw [A_smul, ω, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hq] at h
  convert h using 1
  funext m
  rw [mul_pow, ← pow_mul, mul_comm u m]
  ring

/-- The coefficients of `Mj j`. -/
def mjc (j : ℕ) (m : ℕ) : ℂ := if 3 ∣ j + m then (σ 1 m : ℂ) else 0

lemma mjc_eq {j : ℕ} (hj : ¬ 3 ∣ j) (m : ℕ) :
    mjc j m = ∑ u : Fin 3, wM j u * (e2c m * ω ^ ((u : ℕ) * m)) := by
  have hsum : ∑ u : Fin 3, wM j u * (e2c m * ω ^ ((u : ℕ) * m)) =
      -(1 / 72) * e2c m * ∑ u : Fin 3, ω ^ ((j + m) * (u : ℕ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    simp only [wM]
    rw [add_mul, pow_add, mul_comm m (u : ℕ)]
    ring
  rw [hsum, sum_ω_pow, mjc]
  by_cases h : 3 ∣ j + m
  · have hm : m ≠ 0 := by rintro rfl; exact hj (by simpa using h)
    simp [h, e2c, hm]
    ring
  · simp [h]

lemma hasSum_Mj {j : ℕ} (hj : ¬ 3 ∣ j) (z : ℍ) :
    HasSum (fun m : ℕ ↦ mjc j m * cexp (2 * Real.pi * Complex.I * z) ^ m) (Mj j hj z) := by
  rw [Mj_apply]
  have h := hasSum_sum (s := Finset.univ) fun (u : Fin 3) _ ↦
    (hasSum_E2_A (u : ℕ) z).mul_left (wM j u)
  convert h using 1
  funext m
  rw [mjc_eq hj, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  ring

end

end Eis

open Eis in
theorem exists_H0 : ∃ f : ModularForm (CongruenceSubgroup.Gamma0 9) 2,
    ∀ n : ℕ, (qExpansion 1 f).coeff n = (h0Coeff n : ℂ) :=
  ⟨H0, coeff_eq_of_hasSum H0 _ hasSum_H0⟩

open Eis in
theorem exists_M1 : ∃ f : ModularForm (CongruenceSubgroup.Gamma0 9) 2,
    ∀ n : ℕ, (qExpansion 1 f).coeff n = (m1Coeff n : ℂ) := by
  refine ⟨Mj 2 (by norm_num), fun n ↦ ?_⟩
  rw [coeff_eq_of_hasSum _ _ (hasSum_Mj (by norm_num)) n, mjc, m1Coeff]
  by_cases h : n % 3 = 1
  · have : 3 ∣ 2 + n := by omega
    simp [h, this]
  · have : ¬ 3 ∣ 2 + n := by omega
    simp [h, this]

open Eis in
theorem exists_M2 : ∃ f : ModularForm (CongruenceSubgroup.Gamma0 9) 2,
    ∀ n : ℕ, (qExpansion 1 f).coeff n = (m2Coeff n : ℂ) := by
  refine ⟨Mj 1 (by norm_num), fun n ↦ ?_⟩
  rw [coeff_eq_of_hasSum _ _ (hasSum_Mj (by norm_num)) n, mjc, m2Coeff]
  by_cases h : n % 3 = 2
  · have : 3 ∣ 1 + n := by omega
    simp [h, this]
  · have : ¬ 3 ∣ 1 + n := by omega
    simp [h, this]

end KeithZanello.Modular
