import KZ73.Tree

/-!
# Kernel check of condition (S) (the paper's Remark 16(2), at `p = 73`)

For each odd `w < 4096`, the set `R(w)` of residues modulo 73 of the `M ∈ [M_min, 3000]` with
`c_w(M)` odd is computed as a 73-bit mask. Condition (S) for `(e, ρ)` asks for a double class `c`
with `e M + c ≡ ρ`, that is `M ≡ e⁻¹ (ρ - c) (mod 73)` for some `M ∈ R(w)`. When `R(w)` is
everything this holds for any double class; otherwise the double classes are searched.
The double classes come with explicit witness pairs, computed by `scratch/double_classes.gp`
and checked here.
-/

open PowerSeries

namespace KeithZanello

/-! ## Double classes -/

/-- The 36 double classes of `S₁`, each with two pentagonal indices. -/
def dbl1 : List (ℕ × ℤ × ℤ) :=
  [(0, -146, -97), (1, -145, -98), (2, -96, -74), (4, -90, -80), (5, -144, -99), (6, -126, -117),
   (7, -95, -75), (9, -87, -83), (11, -130, -113), (12, -143, -100), (15, -94, -76),
   (19, -138, -105), (21, -127, -116), (22, -142, -101), (26, -93, -77), (27, -89, -81),
   (28, -133, -110), (30, -135, -108), (35, -141, -102), (38, -131, -112), (39, -128, -115),
   (40, -92, -78), (41, -86, -84), (44, -137, -106), (49, -122, -121), (51, -140, -103),
   (52, -123, -120), (53, -88, -82), (57, -91, -79), (58, -124, -119), (60, -129, -114),
   (64, -134, -109), (67, -125, -118), (68, -132, -111), (70, -139, -104), (72, -136, -107)]

/-- The 36 double classes of `S₃`, each with two triangular indices. -/
def dbl3 : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 72), (1, 1, 71), (3, 2, 70), (5, 12, 60), (6, 3, 69), (7, 17, 55), (8, 24, 48),
   (10, 4, 68), (11, 34, 38), (12, 21, 51), (13, 27, 45), (15, 5, 67), (17, 32, 40), (18, 13, 59),
   (21, 6, 66), (25, 18, 54), (27, 30, 42), (28, 7, 65), (32, 14, 58), (33, 25, 47), (34, 22, 50),
   (36, 8, 64), (41, 28, 44), (44, 19, 53), (45, 9, 63), (46, 35, 37), (47, 15, 57), (50, 33, 39),
   (55, 10, 62), (57, 23, 49), (58, 31, 41), (59, 26, 46), (63, 16, 56), (64, 20, 52),
   (66, 11, 61), (70, 29, 43)]

theorem dbl1_ok : ∀ x ∈ dbl1, |x.2.1| ≤ 146 ∧ |x.2.2| ≤ 146 ∧ pentagonal x.2.1 % 73 = x.1 ∧
    pentagonal x.2.2 % 73 = x.1 ∧ pentagonal x.2.1 % 5329 ≠ pentagonal x.2.2 % 5329 := by
  decide +kernel

theorem dbl3_ok : ∀ x ∈ dbl3, x.2.1 ≤ 146 ∧ x.2.2 ≤ 146 ∧ x.2.1 * (x.2.1 + 1) / 2 % 73 = x.1 ∧
    x.2.2 * (x.2.2 + 1) / 2 % 73 = x.1 ∧
    x.2.1 * (x.2.1 + 1) / 2 % 5329 ≠ x.2.2 * (x.2.2 + 1) / 2 % 5329 := by
  decide +kernel

theorem doubleClass1_of_mem {c : ℕ} (h : c ∈ dbl1.map Prod.fst) : c < 73 ∧ DoubleClass1 c := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨h1, h2, h3, h4, h5⟩ := dbl1_ok x hx
  exact ⟨h3 ▸ Nat.mod_lt _ (by norm_num), x.2.1, x.2.2, h1, h2, h3, h4, h5⟩

theorem doubleClass3_of_mem {c : ℕ} (h : c ∈ dbl3.map Prod.fst) : c < 73 ∧ DoubleClass3 c := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨h1, h2, h3, h4, h5⟩ := dbl3_ok x hx
  exact ⟨h3 ▸ Nat.mod_lt _ (by norm_num), x.2.1, x.2.2, h1, h2, h3, h4, h5⟩

/-! ## Arithmetic modulo 73 -/

/-- The inverse of `e` modulo 73 (Fermat). -/
def inv73 (e : ℕ) : ℕ := e ^ 71 % 73

theorem inv73_ok : ∀ e ∈ pow2List, e * inv73 e % 73 = 1 := by decide +kernel

theorem mod_73_solve {e c ρ M : ℕ} (he : e * inv73 e % 73 = 1) (hc : c < 73)
    (hM : M % 73 = inv73 e * (ρ + 73 - c) % 73) : (e * M + c) % 73 = ρ % 73 := by
  have h1 : M ≡ inv73 e * (ρ + 73 - c) [MOD 73] := hM
  have h2 : e * M + c ≡ e * inv73 e * (ρ + 73 - c) + c [MOD 73] := by
    rw [mul_assoc]; exact (h1.mul_left e).add_right c
  have h4 : e * inv73 e ≡ 1 [MOD 73] := he
  have h5 : e * inv73 e * (ρ + 73 - c) + c ≡ 1 * (ρ + 73 - c) + c [MOD 73] :=
    (h4.mul_right _).add_right c
  have h6 : 1 * (ρ + 73 - c) + c = ρ + 1 * 73 := by omega
  have h7 := h2.trans h5
  rw [h6] at h7
  have h8 : (e * M + c) % 73 = (ρ + 1 * 73) % 73 := h7
  rw [h8, Nat.add_mul_mod_self_right]

/-! ## Residue masks -/

/-- `or` of the chunks `0, …, n-1` of width 73 of `B`. -/
def orChunks (B : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ((B >>> (73 * n)) &&& mask 73) ||| orChunks B n

theorem testBit_orChunks (B n ρ : ℕ) (h : (orChunks B n).testBit ρ = true) :
    ρ < 73 ∧ ∃ k, B.testBit (73 * k + ρ) = true := by
  induction n with
  | zero => simp [orChunks] at h
  | succ n ih =>
    rw [orChunks, Nat.testBit_lor, Nat.testBit_land, Nat.testBit_shiftRight, testBit_mask,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨h2, n, h1⟩
    · exact ih h

/-- Residues modulo 73 of the set bits of `B` at positions `≥ lo` (and `< 73 · 42`). -/
def resMask (B lo : ℕ) : ℕ := orChunks ((B >>> lo) <<< lo) 42

theorem testBit_resMask {B lo ρ : ℕ} (h : (resMask B lo).testBit ρ = true) :
    ∃ M, lo ≤ M ∧ M % 73 = ρ ∧ B.testBit M = true := by
  obtain ⟨hρ, k, hk⟩ := testBit_orChunks _ _ _ h
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_shiftRight] at hk
  refine ⟨73 * k + ρ, hk.1, by omega, ?_⟩
  have := hk.2; rwa [show lo + (73 * k + ρ - lo) = 73 * k + ρ by omega] at this

/-- The test of Remark 16(2) for one `w`, given the bits `B` of `fbar ^ w mod q^3001`. -/
def sLeaf (lo : ℕ) (D : List ℕ) (B : ℕ) : Bool :=
  let R := resMask B lo
  R == mask 73 ||
    pow2List.all fun e ↦ (List.range 73).all fun ρ ↦ D.any fun c ↦ R.testBit (inv73 e * (ρ + 73 - c) % 73)

theorem sLeaf_sound {lo : ℕ} {D : List ℕ} {B : ℕ} (hD : D ≠ []) (h : sLeaf lo D B = true) :
    ∀ e ∈ pow2List, ∀ ρ < 73, ∃ c ∈ D, (resMask B lo).testBit (inv73 e * (ρ + 73 - c) % 73) = true := by
  intro e he ρ hρ
  simp only [sLeaf, Bool.or_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    List.mem_range] at h
  rcases h with h | h
  · obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil D hD
    refine ⟨c, hc, ?_⟩
    rw [h, testBit_mask]; simpa using Nat.mod_lt _ (by norm_num)
  · exact h e he ρ hρ

/-- The conclusion of the test for one `w`. -/
theorem condS_of_sLeaf {lo w B : ℕ} {D : List ℕ} {P : ℕ → Prop}
    (hDP : ∀ c ∈ D, c < 73 ∧ P c) (hD : D ≠ []) (hB : Rep B 3001 (fbar ^ w))
    (h : sLeaf lo D B = true) :
    ∀ e ∈ pow2List, ∀ ρ < 73,
      ∃ M c, lo ≤ M ∧ M ≤ 3000 ∧ coeff M (fbar ^ w) = 1 ∧ P c ∧ (e * M + c) % 73 = ρ := by
  intro e he ρ hρ
  obtain ⟨c, hcD, hc⟩ := sLeaf_sound hD h e he ρ hρ
  obtain ⟨M, hM1, hM2, hM3⟩ := testBit_resMask hc
  have hM4 : M < 3001 := by
    by_contra hM; rw [hB.testBit_ge (by omega)] at hM3; exact absurd hM3 (by decide)
  obtain ⟨hc73, hPc⟩ := hDP c hcD
  refine ⟨M, c, hM1, by omega, (hB.coeff_eq_one_iff hM4).mpr hM3, hPc, ?_⟩
  rw [mod_73_solve (ρ := ρ) (inv73_ok e he) hc73 hM2]
  exact Nat.mod_eq_of_lt hρ

/-! ## The sweep over `w` -/

/-- Traverse the digits `i, …, 11` of `w`; `B` holds the bits of `fbar ^ w mod q^3001`. -/
def sweepS (lo : ℕ) (D : List ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, B, _, _ => sLeaf lo D B
  | fuel + 1, B, w, i =>
    sweepS lo D fuel B w (i + 1) && sweepS lo D fuel (mulPent B (2 ^ i) 3001) (w + 2 ^ i) (i + 1)

theorem sweepS_sound {lo : ℕ} {D : List ℕ} {P : ℕ → Prop}
    (hDP : ∀ c ∈ D, c < 73 ∧ P c) (hD : D ≠ []) :
    ∀ fuel B w i, i + fuel = 12 → w < 2 ^ i → Rep B 3001 (fbar ^ w) → sweepS lo D fuel B w i = true →
      ∀ w' < 4096, w' % 2 ^ i = w → ∀ e ∈ pow2List, ∀ ρ < 73,
        ∃ M c, lo ≤ M ∧ M ≤ 3000 ∧ coeff M (fbar ^ w') = 1 ∧ P c ∧ (e * M + c) % 73 = ρ := by
  intro fuel
  induction fuel with
  | zero =>
    intro B w i hi hw hB hs w' hw' hmod
    obtain rfl : i = 12 := by omega
    obtain rfl : w' = w := by rw [← hmod, Nat.mod_eq_of_lt (by norm_num; omega)]
    exact condS_of_sLeaf hDP hD hB hs
  | succ fuel ih =>
    intro B w i hi hw hB hs w' hw' hmod
    simp only [sweepS, Bool.and_eq_true] at hs
    have hw2 : w + 2 ^ i < 2 ^ (i + 1) := by rw [pow_succ]; omega
    have hB' : Rep (mulPent B (2 ^ i) 3001) 3001 (fbar ^ (w + 2 ^ i)) := by
      rw [pow_add]; exact rep_mulPent_two_pow B 3001 i _ hB
    rcases mod_two_pow_succ_cases hmod with h' | h'
    · exact ih B w (i + 1) (by omega) (by rw [pow_succ]; omega) hB hs.1 w' hw' h'
    · exact ih _ _ (i + 1) (by omega) hw2 hB' hs.2 w' hw' h'

/-- The sweep of the odd `w < 4096` with `w ≡ w₀ (mod 8)`. -/
def sweepSFrom (lo : ℕ) (D : List ℕ) (w₀ : ℕ) : Bool := sweepS lo D 9 (mulDigits 3001 3 w₀ 0 1) w₀ 3

theorem sweepSFrom_sound {lo : ℕ} {D : List ℕ} {P : ℕ → Prop}
    (hDP : ∀ c ∈ D, c < 73 ∧ P c) (hD : D ≠ []) {w₀ : ℕ} (hw₀ : w₀ < 8)
    (h : sweepSFrom lo D w₀ = true) :
    ∀ w' < 4096, w' % 8 = w₀ → ∀ e ∈ pow2List, ∀ ρ < 73,
      ∃ M c, lo ≤ M ∧ M ≤ 3000 ∧ coeff M (fbar ^ w') = 1 ∧ P c ∧ (e * M + c) % 73 = ρ := by
  have hB := rep_mulDigits 3001 3 w₀ 0 1 1 (rep_one _ (by norm_num)) (by norm_num; omega)
  simp only [one_mul, pow_zero] at hB
  exact sweepS_sound hDP hD 9 _ w₀ 3 rfl (by norm_num; omega) hB h

theorem sweepS1_1 : sweepSFrom 1 (dbl1.map Prod.fst) 1 = true := by decide +kernel
theorem sweepS1_3 : sweepSFrom 1 (dbl1.map Prod.fst) 3 = true := by decide +kernel
theorem sweepS1_5 : sweepSFrom 1 (dbl1.map Prod.fst) 5 = true := by decide +kernel
theorem sweepS1_7 : sweepSFrom 1 (dbl1.map Prod.fst) 7 = true := by decide +kernel
theorem sweepS3_1 : sweepSFrom 3 (dbl3.map Prod.fst) 1 = true := by decide +kernel
theorem sweepS3_3 : sweepSFrom 3 (dbl3.map Prod.fst) 3 = true := by decide +kernel
theorem sweepS3_5 : sweepSFrom 3 (dbl3.map Prod.fst) 5 = true := by decide +kernel
theorem sweepS3_7 : sweepSFrom 3 (dbl3.map Prod.fst) 7 = true := by decide +kernel

/-- **Condition (S) for `τ = 1`** (kernel-checked). -/
theorem condS1 : CondS1 := by
  intro w hw hodd
  have hDP : ∀ c ∈ dbl1.map Prod.fst, c < 73 ∧ DoubleClass1 c := fun c h ↦ doubleClass1_of_mem h
  have hD : dbl1.map Prod.fst ≠ [] := by decide
  have h8 : w % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h8' : w % 8 % 2 = 1 := by omega
  obtain h | h | h | h : w % 8 = 1 ∨ w % 8 = 3 ∨ w % 8 = 5 ∨ w % 8 = 7 := by omega
  · exact sweepSFrom_sound hDP hD (by norm_num) sweepS1_1 w hw h
  · exact sweepSFrom_sound hDP hD (by norm_num) sweepS1_3 w hw h
  · exact sweepSFrom_sound hDP hD (by norm_num) sweepS1_5 w hw h
  · exact sweepSFrom_sound hDP hD (by norm_num) sweepS1_7 w hw h

/-- **Condition (S) for `τ = 3`** (kernel-checked). -/
theorem condS3 : CondS3 := by
  intro w hw hodd
  have hDP : ∀ c ∈ dbl3.map Prod.fst, c < 73 ∧ DoubleClass3 c := fun c h ↦ doubleClass3_of_mem h
  have hD : dbl3.map Prod.fst ≠ [] := by decide
  obtain h | h | h | h : w % 8 = 1 ∨ w % 8 = 3 ∨ w % 8 = 5 ∨ w % 8 = 7 := by omega
  · exact sweepSFrom_sound hDP hD (by norm_num) sweepS3_1 w hw h
  · exact sweepSFrom_sound hDP hD (by norm_num) sweepS3_3 w hw h
  · exact sweepSFrom_sound hDP hD (by norm_num) sweepS3_5 w hw h
  · exact sweepSFrom_sound hDP hD (by norm_num) sweepS3_7 w hw h

end KeithZanello
