/-
Ported from the Prove2Me proof repository github.com/anthropics/fermats-last-theorem,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, source files
  P2M/Sol/S_UpperHalfPlane_qExpansion_prod.lean
  P2M/Sol/S_UpperHalfPlane_qExpansion_coeff_nat_mul.lean
  P2M/Sol/S_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj.lean
  P2M/Sol/S_ModularForm_levelOne_eq_zero_of_lt_order_qExpansion.lean
  P2M/Sol/S_ModularForm_eq_zero_of_lt_order_qExpansion_of_isArithmetic.lean
  P2M/Sol/S_ModularForm_sturm_bound_of_isArithmetic.lean
  P2M/Sol/S_ModularForm_sturm_bound_Gamma0.lean
(statements in the matching Theorems/Thm_*.lean files).
Apache License 2.0, Copyright 2026 Anthropic, PBC.
Adapted to Lean 4.34.1 and Mathlib v4.34.1: the `p2m_*` commands are removed and the results
are stated in the namespace `KeithZanello.Modular.P2M`.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Complex Sturm bound on `Γ₀(N)`

A modular form of weight `k` on `Γ₀(N)` whose `q`-expansion coefficients of index
`≤ k [SL₂(ℤ) : Γ₀(N)] / 12` vanish is zero.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Function UpperHalfPlane ModularForm SlashInvariantForm SlashInvariantFormClass
  ModularFormClass Matrix.SpecialLinearGroup ConjAct

open scoped Real MatrixGroups ModularForm Topology Manifold Pointwise

namespace KeithZanello.Modular.P2M

/-- The `q`-expansion of a finite product of functions with analytic cusp functions. -/
theorem qExpansion_prod {h : ℝ} {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ}
    (hF : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction h (F i)) 0) :
    qExpansion h (∏ i ∈ s, F i) = ∏ i ∈ s, qExpansion h (F i) := by
  suffices H : qExpansion h (∏ i ∈ s, F i) = ∏ i ∈ s, qExpansion h (F i) ∧
      AnalyticAt ℂ (cuspFunction h (∏ i ∈ s, F i)) 0 from H.1
  induction s using Finset.cons_induction with
  | empty =>
    have h1 : cuspFunction h (1 : ℍ → ℂ) = 1 := by
      ext q
      rcases eq_or_ne q 0 with rfl | hq
      · simp [cuspFunction, Periodic.cuspFunction]
        exact Filter.Tendsto.limUnder_eq tendsto_const_nhds
      · simp [cuspFunction, Periodic.cuspFunction_eq_of_nonzero h _ hq]
    refine ⟨by simpa using qExpansion_one h, ?_⟩
    rw [Finset.prod_empty, h1]
    exact analyticAt_const
  | cons a s ha ih =>
    have hFa : AnalyticAt ℂ (cuspFunction h (F a)) 0 := hF a (Finset.mem_cons_self a s)
    obtain ⟨ih1, ih2⟩ := ih fun i hi ↦ hF i (Finset.mem_cons_of_mem hi)
    rw [Finset.prod_cons, Finset.prod_cons, qExpansion_mul hFa ih2, ih1]
    refine ⟨rfl, ?_⟩
    rw [cuspFunction_mul hFa.continuousAt ih2.continuousAt]
    exact hFa.mul ih2

/-- A bare function type with a trivial `FunLike` instance, used to apply
`qExpansion_coeff_unique` to an arbitrary function `ℍ → ℂ`. -/
def FnLike : Type := ℍ → ℂ

scoped instance : FunLike FnLike ℍ ℂ where
  coe f := f
  coe_injective _ _ h := h

/-- Coefficients of the `q`-expansion with respect to the period `M h`. -/
theorem qExpansion_coeff_nat_mul {h : ℝ} (hh : 0 < h) {F : ℍ → ℂ}
    (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) h) (hhol : MDiff F)
    (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) {M : ℕ} (hM : 0 < M) (n : ℕ) :
    (qExpansion (M * h) F).coeff n = if M ∣ n then (qExpansion h F).coeff (n / M) else 0 := by
  have hMh : 0 < (M : ℝ) * h := by positivity
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hper' : Periodic (F ∘ ofComplex) (((M : ℝ) * h : ℝ) : ℂ) := by
    simpa using hper.nat_mul M
  have han : AnalyticAt ℂ (cuspFunction (M * h) F) 0 :=
    analyticAt_cuspFunction_zero hMh hper' hhol hbdd
  set c : ℕ → ℂ := fun n ↦ if M ∣ n then (qExpansion h F).coeff (n / M) else 0 with hc
  have hsum : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam (M * h) τ ^ m) (F τ) := by
    intro τ
    have hq : Periodic.qParam h τ = Periodic.qParam (M * h) τ ^ M := by
      simp only [Periodic.qParam, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    have hs := hasSum_qExpansion hh hper hhol hbdd τ
    simp_rw [hq, ← pow_mul] at hs
    have hinj : Injective (fun m : ℕ ↦ M * m) := mul_right_injective₀ hM.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ ↦ M * m),
        (fun m ↦ c m • Periodic.qParam (M * h) τ ^ m) x = 0 := by
      intro x hx
      have : ¬ M ∣ x := by
        rintro ⟨d, rfl⟩
        exact hx ⟨d, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).mp ?_
    convert hs using 1
    ext m
    simp [hc, Nat.mul_div_cancel_left _ hM]
  have key := qExpansion_coeff_unique (F := FnLike) (show FnLike from F) hMh han hsum n
  exact key.symm

/-- An arithmetic subgroup has a common integral strict period at all the cusps. -/
theorem exists_nat_mem_strictPeriods_conj (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] :
    ∃ M : ℕ, 0 < M ∧ ∀ γ : SL(2, ℤ),
      (M : ℝ) ∈ (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ) • 𝒢).strictPeriods := by
  have : (𝒢.comap (mapGL (R := ℤ) ℝ)).FiniteIndex := Subgroup.IsArithmetic.finiteIndex_comap 𝒢
  set Λ : Subgroup SL(2, ℤ) := (𝒢.comap (mapGL (R := ℤ) ℝ)).normalCore with hΛ
  have : Λ.FiniteIndex := inferInstance
  have hN : Λ.Normal := inferInstance
  refine ⟨Λ.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun γ ↦ ?_⟩
  have hT : ModularGroup.T ^ Λ.index ∈ Λ := Λ.pow_index_mem ModularGroup.T
  have hconj : γ⁻¹ * ModularGroup.T ^ Λ.index * γ ∈ 𝒢.comap (mapGL ℝ) := by
    apply Subgroup.normalCore_le
    simpa using hN.conj_mem _ hT γ⁻¹
  have hU : ∀ m : ℤ, Matrix.GeneralLinearGroup.upperRightHom ((m : ℝ)) =
      mapGL ℝ (ModularGroup.T ^ m) := by
    intro m
    simp only [Units.ext_iff, mapGL_coe_matrix, map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow]
  have hU' := hU Λ.index
  rw [zpow_natCast, Int.cast_natCast] at hU'
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ← toConjAct_inv, toConjAct_smul, inv_inv, hU', ← map_inv, ← map_mul, ← map_mul]
  exact hconj

/-- Level one Sturm bound with respect to the period `M`. -/
theorem levelOne_eq_zero_of_lt_order_qExpansion (M : ℕ) (hM : 0 < M) {k : ℤ}
    (F : ModularForm 𝒮ℒ k)
    (h : ((M * (k.toNat / 12) : ℕ) : ℕ∞) < (qExpansion (M : ℝ) F).order) : F = 0 := by
  by_contra hF
  have hq1 : qExpansion 1 F ≠ 0 := by
    rwa [Ne, ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_SL]
  have hord : (qExpansion 1 F).order ≠ ⊤ := by
    rwa [Ne, PowerSeries.order_eq_top]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hord
  have hle : n ≤ k.toNat / 12 := by
    refine le_of_not_gt fun hlt ↦ hF (ModularForm.sturm_bound_levelOne ?_)
    rw [← hn]
    exact_mod_cast hlt
  have hcoeff : (qExpansion 1 F).coeff n ≠ 0 := by
    have := PowerSeries.coeff_order hq1
    rwa [← hn, ENat.toNat_natCast] at this
  have hper := periodic_comp_ofComplex F one_mem_strictPeriods_SL
  have : Fact (IsCusp OnePoint.infty 𝒮ℒ) := ⟨(𝒮ℒ).isCusp_of_mem_strictPeriods one_pos
    one_mem_strictPeriods_SL⟩
  have hM' := qExpansion_coeff_nat_mul one_pos hper (holo F) (bdd_at_infty F) hM (M * n)
  rw [mul_one, ite_eq_left (dvd_mul_right M n), Nat.mul_div_cancel_left _ hM] at hM'
  have hordM : (qExpansion (M : ℝ) F).order ≤ (M * n : ℕ) :=
    PowerSeries.order_le _ (by rwa [hM'])
  have : ((M * n : ℕ) : ℕ∞) ≤ (M * (k.toNat / 12) : ℕ) := by
    exact_mod_cast Nat.mul_le_mul_left M hle
  exact absurd (h.trans_le (hordM.trans this)) (lt_irrefl _)

theorem analyticAt_cuspFunction_quotientFunc {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    {k : ℤ} (f : ModularForm 𝒢 k) {M : ℕ} (hM : 0 < M)
    (hconj : ∀ γ : SL(2, ℤ), (M : ℝ) ∈ (toConjAct (mapGL ℝ γ) • 𝒢).strictPeriods)
    (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :
    AnalyticAt ℂ (cuspFunction M (quotientFunc f q)) 0 := by
  induction q using Quotient.inductionOn with
  | h r =>
    obtain ⟨γ, hγ⟩ := r.2
    have hp : (M : ℝ) ∈ (toConjAct (r.1⁻¹)⁻¹ • 𝒢).strictPeriods := by
      rw [inv_inv, ← hγ]
      exact hconj γ
    exact ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.translate f r.1⁻¹)
      (Nat.cast_pos.mpr hM) hp

/-- Sturm bound for an arithmetic subgroup, with respect to a common period `M` of all cusps. -/
theorem eq_zero_of_lt_order_qExpansion_of_isArithmetic {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    [𝒢.IsArithmetic] {k : ℤ} (f : ModularForm 𝒢 k) {M : ℕ} (hM : 0 < M)
    (hconj : ∀ γ : SL(2, ℤ), (M : ℝ) ∈
      (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ) • 𝒢).strictPeriods)
    (h : ((M * ((k * 𝒢.relIndex 𝒮ℒ).toNat / 12) : ℕ) : ℕ∞) < (qExpansion M f).order) :
    f = 0 := by
  set F := ModularForm.norm 𝒮ℒ f with hF
  have hanalytic := analyticAt_cuspFunction_quotientFunc f hM hconj
  let _ : Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  have hprod : qExpansion M F = ∏ q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ, qExpansion M (quotientFunc f q) := by
    rw [hF, ModularForm.coe_norm]
    exact qExpansion_prod Finset.univ fun q _ ↦ hanalytic q
  have hone : quotientFunc f (⟦1⟧ : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) = ⇑f := by
    rw [quotientFunc_mk]
    simp
  have horder : (qExpansion M f).order ≤ (qExpansion M F).order := by
    rw [hprod, PowerSeries.order_prod, ← hone]
    exact Finset.single_le_sum (f := fun q ↦ (qExpansion M (quotientFunc f q)).order)
      (fun _ _ ↦ zero_le) (Finset.mem_univ _)
  have hrel : 𝒢.relIndex 𝒮ℒ = Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := rfl
  have hF0 : F = 0 := by
    refine levelOne_eq_zero_of_lt_order_qExpansion M hM F (lt_of_lt_of_le ?_ horder)
    simpa [hrel] using h
  rw [hF, ModularForm.norm_eq_zero_iff] at hF0
  exact DFunLike.coe_injective (hF0.trans FunLike.coe_zero.symm)

/-- Sturm bound for an arithmetic subgroup having `1` as a strict period at `∞`. -/
theorem sturm_bound_of_isArithmetic {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] {k : ℤ}
    {f : ModularForm 𝒢 k} (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods)
    (h : (↑((k * 𝒢.relIndex 𝒮ℒ).toNat / 12) : ℕ∞) < (qExpansion 1 f).order) : f = 0 := by
  obtain ⟨M, hM, hconj⟩ := exists_nat_mem_strictPeriods_conj 𝒢
  have : Fact (IsCusp OnePoint.infty 𝒢) := ⟨𝒢.isCusp_of_mem_strictPeriods one_pos h1⟩
  refine eq_zero_of_lt_order_qExpansion_of_isArithmetic f hM hconj ?_
  refine lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _)
    (PowerSeries.nat_le_order _ _ fun n hn ↦ ?_)
  have := qExpansion_coeff_nat_mul one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f h1) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) hM n
  rw [mul_one] at this
  rw [this]
  split_ifs with hd
  · apply PowerSeries.coeff_of_lt_order
    refine lt_of_le_of_lt ?_ h
    exact_mod_cast Nat.div_le_of_le_mul (by lia)
  · rfl

theorem relIndex_map_mapGL (Γ : Subgroup SL(2, ℤ)) :
    (Γ : Subgroup (GL (Fin 2) ℝ)).relIndex 𝒮ℒ = Γ.index := by
  rw [← Subgroup.index_comap, Subgroup.comap_map_eq_self_of_injective mapGL_injective]

/-- Complex Sturm bound on `Γ₀(N)`. -/
theorem sturm_bound_Gamma0 (N : ℕ) [NeZero N] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (h : ∀ n : ℕ, n ≤ (k * (CongruenceSubgroup.Gamma0 N).index).toNat / 12 →
      (qExpansion 1 f).coeff n = 0) : f = 0 := by
  have h1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [CongruenceSubgroup.strictPeriods_Gamma0]
  refine sturm_bound_of_isArithmetic h1 ?_
  rw [relIndex_map_mapGL]
  refine lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _)
    (PowerSeries.nat_le_order _ _ fun n hn ↦ ?_)
  exact h n (by lia)

end KeithZanello.Modular.P2M
