import KZ73.Modular.Arith
import KZ73.Modular.Eisenstein
import KZ73.Modular.SturmBound

/-!
# Sturm's theorem modulo 2 on `Γ₀(9)`

A modular form of weight `2 j` on `Γ₀(9)` with integer `q`-expansion whose coefficients of index
`≤ 2 j` are even has all its coefficients even.

Proof: the monomials `H₀^a M₁^b F₂^c` (`a + b + c = j`) have integer expansions of order
`b + 2 c` with leading coefficient 1 (`exists_basis`), so an integral form can be reduced, by
subtracting even multiples of them in increasing order, to a form whose coefficients of index
`≤ 2 j` vanish; by the complex Sturm bound on `Γ₀(9)` that form is zero (`sturm_mod_two`).
-/

open UpperHalfPlane PowerSeries

namespace KeithZanello.Modular

/-- `Γ₀(9)` as a subgroup of `GL(2, ℝ)`. -/
abbrev Γ9 : Subgroup (GL (Fin 2) ℝ) := CongruenceSubgroup.Gamma0 9

theorem one_mem_strictPeriods_Γ9 : (1 : ℝ) ∈ Γ9.strictPeriods := by simp

/-- `f` has the integer `q`-expansion `P`. -/
def HasIntQExp {k : ℤ} (f : ModularForm Γ9 k) (P : ℤ⟦X⟧) : Prop :=
  ∀ n : ℕ, (qExpansion 1 f).coeff n = ((coeff n P : ℤ) : ℂ)

namespace HasIntQExp

variable {k k' : ℤ} {f : ModularForm Γ9 k} {g : ModularForm Γ9 k'} {P Q : ℤ⟦X⟧}

theorem mul (hf : HasIntQExp f P) (hg : HasIntQExp g Q) : HasIntQExp (f.mul g) (P * Q) := by
  intro n
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_Γ9, coeff_mul, coeff_mul,
    Int.cast_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [hf, hg, Int.cast_mul]

theorem add {g : ModularForm Γ9 k} (hf : HasIntQExp f P) (hg : HasIntQExp g Q) :
    HasIntQExp (f + g) (P + Q) := by
  intro n
  rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_Γ9, map_add,
    map_add, hf, hg, Int.cast_add]

theorem sub_smul {g : ModularForm Γ9 k} (hf : HasIntQExp f P) (hg : HasIntQExp g Q) (c : ℤ) :
    HasIntQExp (f - (c : ℂ) • g) (P - c • Q) := by
  intro n
  rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_Γ9,
    FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_Γ9, map_sub, map_sub, map_smul,
    map_zsmul, hf, hg, smul_eq_mul, smul_eq_mul, Int.cast_sub, Int.cast_mul]

theorem mcast {k'' : ℤ} (h : k = k'') (hf : HasIntQExp f P) : HasIntQExp (f.mcast h) P := hf

theorem pow (hf : HasIntQExp f P) (t : ℕ) : HasIntQExp (f.pow t) (P ^ t) := by
  intro n
  rw [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_Γ9]
  have : qExpansion 1 f = PowerSeries.map (Int.castRingHom ℂ) P := by
    ext m; rw [hf, coeff_map]; rfl
  rw [this, ← map_pow, coeff_map]; rfl

end HasIntQExp

theorem hasIntQExp_one : HasIntQExp (1 : ModularForm Γ9 0) 1 := by
  intro n
  rw [ModularForm.qExpansion_one, coeff_one, coeff_one]
  split_ifs <;> simp

/-! ## The three weight 2 forms with integer expansions -/

theorem exists_H0' : ∃ f : ModularForm Γ9 2, HasIntQExp f h0z := by
  obtain ⟨f, hf⟩ := exists_H0
  exact ⟨f, fun n ↦ by rw [hf, coeff_h0z]⟩

theorem exists_M1' : ∃ f : ModularForm Γ9 2, HasIntQExp f m1z := by
  obtain ⟨f, hf⟩ := exists_M1
  exact ⟨f, fun n ↦ by rw [hf, coeff_m1z]⟩

theorem exists_F2 : ∃ f : ModularForm Γ9 2, HasIntQExp f f2z := by
  obtain ⟨f, hf⟩ := exists_M2
  refine ⟨(1 / 3 : ℂ) • f, fun n ↦ ?_⟩
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_Γ9, map_smul,
    hf, m2Coeff_eq, coeff_f2z, smul_eq_mul]
  push_cast
  ring

theorem exists_L : ∃ f : ModularForm Γ9 2, HasIntQExp f lz := by
  obtain ⟨f, hf⟩ := exists_M1
  obtain ⟨g, hg⟩ := exists_M2
  refine ⟨f + g, fun n ↦ ?_⟩
  rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_Γ9, map_add,
    hf, hg, coeff_lz, Int.cast_add]

/-! ## Orders of products -/

/-- `P` has order `m` and leading coefficient `u`. -/
def OrdLead (P : ℤ⟦X⟧) (m : ℕ) (u : ℤ) : Prop := (∀ n < m, coeff n P = 0) ∧ coeff m P = u

theorem OrdLead.mul {P Q : ℤ⟦X⟧} {a b : ℕ} {u v : ℤ} (hP : OrdLead P a u) (hQ : OrdLead Q b v) :
    OrdLead (P * Q) (a + b) (u * v) := by
  obtain ⟨P₁, rfl⟩ := (X_pow_dvd_iff).mpr hP.1
  obtain ⟨Q₁, rfl⟩ := (X_pow_dvd_iff).mpr hQ.1
  have hu : coeff 0 P₁ = u := by
    have := hP.2; rwa [coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self] at this
  have hv : coeff 0 Q₁ = v := by
    have := hQ.2; rwa [coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self] at this
  have hPQ : X ^ a * P₁ * (X ^ b * Q₁) = X ^ (a + b) * (P₁ * Q₁) := by ring
  rw [hPQ]
  refine ⟨fun n hn ↦ ?_, ?_⟩
  · rw [coeff_X_pow_mul', ite_eq_right (by omega)]
  · rw [coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_mul,
      ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, hu, hv]

theorem ordLead_h0z : OrdLead h0z 0 1 := ⟨fun n hn ↦ absurd hn (Nat.not_lt_zero n), coeff_zero_h0z⟩

theorem ordLead_m1z : OrdLead m1z 1 1 :=
  ⟨fun n hn ↦ by obtain rfl : n = 0 := by omega
                 exact coeff_zero_m1z, coeff_one_m1z⟩

theorem ordLead_f2z : OrdLead f2z 2 1 :=
  ⟨fun n hn ↦ by
    interval_cases n
    · exact coeff_zero_f2z
    · exact coeff_one_f2z, coeff_two_f2z⟩

/-! ## The triangular basis -/

/-- In weight `2 j`, for every `m ≤ 2 j` there is a form with integer expansion of order `m`
and leading coefficient 1. -/
theorem exists_basis (j : ℕ) : ∀ m ≤ 2 * j, ∃ (B : ModularForm Γ9 ((2 * j : ℕ) : ℤ)) (P : ℤ⟦X⟧),
    HasIntQExp B P ∧ OrdLead P m 1 := by
  induction j with
  | zero =>
    intro m hm
    obtain rfl : m = 0 := by omega
    refine ⟨(1 : ModularForm Γ9 0).mcast (by simp), 1, hasIntQExp_one.mcast _, ?_, ?_⟩
    · intro n hn; omega
    · simp
  | succ j ih =>
    intro m hm
    obtain ⟨H, hH⟩ := exists_H0'
    obtain ⟨M, hM⟩ := exists_M1'
    obtain ⟨F, hF⟩ := exists_F2
    have hw : (2 : ℤ) + ((2 * j : ℕ) : ℤ) = ((2 * (j + 1) : ℕ) : ℤ) := by push_cast; ring
    rcases Nat.lt_or_ge (2 * j) m with hlt | hle
    · rcases (show m = 2 * j + 1 ∨ m = 2 * j + 2 by omega) with rfl | rfl
      · obtain ⟨B, P, hB, hP⟩ := ih (2 * j) le_rfl
        refine ⟨(M.mul B).mcast hw, m1z * P, (hM.mul hB).mcast hw, ?_⟩
        have := ordLead_m1z.mul hP
        rwa [one_mul, show 1 + 2 * j = 2 * j + 1 by ring] at this
      · obtain ⟨B, P, hB, hP⟩ := ih (2 * j) le_rfl
        refine ⟨(F.mul B).mcast hw, f2z * P, (hF.mul hB).mcast hw, ?_⟩
        have := ordLead_f2z.mul hP
        rwa [one_mul, show 2 + 2 * j = 2 * j + 2 by ring] at this
    · obtain ⟨B, P, hB, hP⟩ := ih m hle
      refine ⟨(H.mul B).mcast hw, h0z * P, (hH.mul hB).mcast hw, ?_⟩
      have := ordLead_h0z.mul hP
      rwa [one_mul, zero_add] at this

/-! ## Sturm's theorem modulo 2 -/

/-- **Sturm's theorem modulo 2 on `Γ₀(9)`.** -/
theorem sturm_mod_two (j : ℕ) (f : ModularForm Γ9 ((2 * j : ℕ) : ℤ)) (P : ℤ⟦X⟧)
    (hf : HasIntQExp f P) (hlow : ∀ n ≤ 2 * j, (2 : ℤ) ∣ coeff n P) :
    ∀ n, (2 : ℤ) ∣ coeff n P := by
  have step : ∀ m ≤ 2 * j + 1, ∃ (g : ModularForm Γ9 ((2 * j : ℕ) : ℤ)) (Q : ℤ⟦X⟧),
      HasIntQExp g Q ∧ (∀ n < m, coeff n Q = 0) ∧ (∀ n ≤ 2 * j, (2 : ℤ) ∣ coeff n Q) ∧
        ∀ n, (2 : ℤ) ∣ coeff n P - coeff n Q := by
    intro m
    induction m with
    | zero => exact fun _ ↦ ⟨f, P, hf, fun n hn ↦ absurd hn (Nat.not_lt_zero n), hlow,
        fun n ↦ by simp⟩
    | succ m ih =>
      intro hm
      obtain ⟨g, Q, hg, hQ0, hQ2, hPQ⟩ := ih (by omega)
      obtain ⟨B, R, hB, hR0, hR1⟩ := exists_basis j m (by omega)
      set c := coeff m Q with hc
      have hc2 : (2 : ℤ) ∣ c := hQ2 m (by omega)
      refine ⟨g - (c : ℂ) • B, Q - c • R, hg.sub_smul hB c, fun n hn ↦ ?_, fun n hn ↦ ?_,
        fun n ↦ ?_⟩
      · rw [map_sub, map_zsmul, smul_eq_mul]
        rcases Nat.lt_or_ge n m with h | h
        · rw [hQ0 n h, hR0 n h, mul_zero, sub_zero]
        · obtain rfl : n = m := by omega
          rw [hR1, mul_one, hc, sub_self]
      · rw [map_sub, map_zsmul, smul_eq_mul]
        exact dvd_sub (hQ2 n hn) (dvd_mul_of_dvd_left hc2 _)
      · rw [map_sub, map_zsmul, smul_eq_mul, sub_sub_eq_add_sub, add_sub_right_comm]
        exact dvd_add (hPQ n) (dvd_mul_of_dvd_left hc2 _)
  obtain ⟨g, Q, hg, hQ0, -, hPQ⟩ := step (2 * j + 1) le_rfl
  have hg0 : g = 0 := sturm_bound_Gamma0_nine g fun n hn ↦ by
    rw [hg, hQ0 n (by simp at hn; omega), Int.cast_zero]
  intro n
  have hQn : coeff n Q = 0 := by
    have := hg n
    rw [hg0, FunLike.coe_zero, qExpansion_zero, map_zero] at this
    exact_mod_cast this.symm
  simpa [hQn] using hPQ n

end KeithZanello.Modular
