import KZ73.Pairs
import KZ73.Jacobi

/-!
# The balls around `1` and `3` (the paper's Lemmas 14 and 15, at `p = 73`)

For `T = 1 + 2^K w` (`K ≥ 13`, `w` odd), `fbar ^ T = fbar · fbar^w(q^(2^K))`, and at the special
indices `N = 2^K M + P_i` (`|i| ≤ 146`, `M ≤ 3000`) only one pentagonal number contributes
(Lemma 14(a)), so `[q^N] fbar^T = [q^M] fbar^w`. For `T = 3 + 2^K w` (`K ≥ 11`) the same holds
with `fbar^3 = ∑ q^(k(k+1)/2)` (Jacobi's identity modulo 2) and triangular numbers.
Parameters: `κ = 146`, `μ = 3000`, `K₀ = 13`, `K₀' = 11` (paper, Section 5).
-/

open PowerSeries

namespace KeithZanello

/-! ## Lemma 14: special indices -/

theorem isCoprime_two_pow_of_odd {b : ℤ} (hb : Odd b) (n : ℕ) : IsCoprime ((2 : ℤ) ^ n) b := by
  obtain ⟨k, rfl⟩ := hb
  exact IsCoprime.pow_left ⟨-k, 1, by ring⟩

theorem le_abs_of_dvd {d x : ℤ} (hd : d ∣ x) (hx : x ≠ 0) : d ≤ |x| :=
  Int.le_of_dvd (abs_pos.mpr hx) ((dvd_abs d x).mpr hd)

/-- **Lemma 14(a)** with `κ = 146`, `μ = 3000`, `K ≥ 13`. -/
theorem special_pent {K : ℕ} (hK : 13 ≤ K) {i₀ i : ℤ} (hi₀ : |i₀| ≤ 146) {M : ℕ} (hM : M ≤ 3000)
    (hle : pentagonal i ≤ 2 ^ K * M + pentagonal i₀)
    (hdvd : (2 : ℤ) ^ K ∣ (pentagonal i : ℤ) - pentagonal i₀) : i = i₀ := by
  by_contra hne
  have hX : (8192 : ℤ) ≤ 2 ^ K := by
    have : (2 : ℤ) ^ 13 ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hK
    norm_num at this; exact this
  set X : ℤ := 2 ^ K with hXdef
  have hP := two_mul_natCast_pentagonal i
  have hP0 := two_mul_natCast_pentagonal i₀
  have h2 : (2 : ℤ) ^ (K + 1) ∣ (i - i₀) * (3 * i + 3 * i₀ - 1) := by
    have e : (i - i₀) * (3 * i + 3 * i₀ - 1) = 2 * ((pentagonal i : ℤ) - pentagonal i₀) := by
      linear_combination hP0 - hP
    rw [e, pow_succ, mul_comm _ (2 : ℤ)]
    exact mul_dvd_mul_left 2 hdvd
  have hX2 : (2 : ℤ) ^ (K + 1) = 2 * X := by rw [pow_succ, hXdef]; ring
  have habs0 : -146 ≤ i₀ ∧ i₀ ≤ 146 := abs_le.mp hi₀
  have hbig : 2 * X - 439 ≤ 3 * |i| := by
    rcases Int.even_or_odd (i - i₀) with he | ho
    · have hodd : Odd (3 * i + 3 * i₀ - 1) := by
        obtain ⟨k, hk⟩ := he; exact ⟨3 * k + 3 * i₀ - 1, by linarith⟩
      have hd := (isCoprime_two_pow_of_odd hodd (K + 1)).dvd_of_dvd_mul_right h2
      have := le_abs_of_dvd hd (sub_ne_zero.mpr hne)
      rw [hX2] at this
      have h3 := abs_sub_abs_le_abs_sub i i₀
      have h4 : |i - i₀| ≤ |i| + |i₀| := abs_sub _ _
      linarith
    · have hd := (isCoprime_two_pow_of_odd ho (K + 1)).dvd_of_dvd_mul_left h2
      have hne0 : 3 * i + 3 * i₀ - 1 ≠ 0 := by omega
      have := le_abs_of_dvd hd hne0
      rw [hX2] at this
      have h4 : |3 * i + 3 * i₀ - 1| ≤ |3 * i| + |3 * i₀ - 1| := by
        have := abs_add_le (3 * i) (3 * i₀ - 1); rwa [← add_sub_assoc] at this
      have h5 : |3 * i₀ - 1| ≤ 439 := abs_le.mpr ⟨by linarith, by linarith⟩
      have h6 : |3 * i| = 3 * |i| := by rw [abs_mul]; norm_num
      linarith
  -- size contradiction
  have hP0b : i₀ * (3 * i₀ - 1) ≤ 64094 := by nlinarith
  have hMz : (M : ℤ) ≤ 3000 := by exact_mod_cast hM
  have hXM : X * M ≤ X * 3000 := by nlinarith
  have hu : 3 * |i| * (3 * |i| - 1) ≤ 3 * (i * (3 * i - 1)) := by
    rcases abs_cases i with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nlinarith
  have hv : (2 * X - 439) * (2 * X - 440) ≤ 3 * |i| * (3 * |i| - 1) := by
    have : 0 ≤ 2 * X - 440 := by linarith
    nlinarith
  nlinarith

/-- **Lemma 14(b)** with `κ = 146`, `μ = 3000`, `K ≥ 11`. -/
theorem special_tri {K : ℕ} (hK : 11 ≤ K) {i₀ i : ℕ} (hi₀ : i₀ ≤ 146) {M : ℕ} (hM : M ≤ 3000)
    (hle : i * (i + 1) / 2 ≤ 2 ^ K * M + i₀ * (i₀ + 1) / 2)
    (hdvd : (2 : ℤ) ^ K ∣ ((i * (i + 1) / 2 : ℕ) : ℤ) - ((i₀ * (i₀ + 1) / 2 : ℕ) : ℤ)) :
    i = i₀ := by
  by_contra hne
  have hle' : ((i * (i + 1) / 2 : ℕ) : ℤ) ≤ 2 ^ K * M + ((i₀ * (i₀ + 1) / 2 : ℕ) : ℤ) := by
    exact_mod_cast hle
  have hX : (2048 : ℤ) ≤ 2 ^ K := by
    have : (2 : ℤ) ^ 11 ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hK
    norm_num at this; exact this
  set X : ℤ := 2 ^ K with hXdef
  have hT : ∀ j : ℕ, 2 * ((j * (j + 1) / 2 : ℕ) : ℤ) = (j : ℤ) * (j + 1) := by
    intro j
    have hn : 2 * (j * (j + 1) / 2) = j * (j + 1) :=
      Nat.mul_div_cancel' (Nat.even_mul_succ_self j).two_dvd
    exact_mod_cast hn
  have hTi := hT i
  have hTi₀ := hT i₀
  have h2 : (2 : ℤ) ^ (K + 1) ∣ ((i : ℤ) - i₀) * (i + i₀ + 1) := by
    have e : ((i : ℤ) - i₀) * (i + i₀ + 1) =
        2 * (((i * (i + 1) / 2 : ℕ) : ℤ) - ((i₀ * (i₀ + 1) / 2 : ℕ) : ℤ)) := by
      linear_combination hTi₀ - hTi
    rw [e, pow_succ, mul_comm _ (2 : ℤ)]
    exact mul_dvd_mul_left 2 hdvd
  have hX2 : (2 : ℤ) ^ (K + 1) = 2 * X := by rw [pow_succ, hXdef]; ring
  have hi₀z : (i₀ : ℤ) ≤ 146 := by exact_mod_cast hi₀
  have hbig : 2 * X - 147 ≤ (i : ℤ) := by
    rcases Int.even_or_odd ((i : ℤ) - i₀) with he | ho
    · have hodd : Odd ((i : ℤ) + i₀ + 1) := by
        obtain ⟨k, hk⟩ := he; exact ⟨k + i₀, by linarith⟩
      have hd := (isCoprime_two_pow_of_odd hodd (K + 1)).dvd_of_dvd_mul_right h2
      have hne' : (i : ℤ) - i₀ ≠ 0 := by
        intro h; apply hne; exact_mod_cast sub_eq_zero.mp h
      have := le_abs_of_dvd hd hne'
      rw [hX2] at this
      rcases abs_cases ((i : ℤ) - i₀) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at this <;> linarith
    · have hd := (isCoprime_two_pow_of_odd ho (K + 1)).dvd_of_dvd_mul_left h2
      have hpos : (0 : ℤ) < i + i₀ + 1 := by positivity
      have := Int.le_of_dvd hpos hd
      rw [hX2] at this
      linarith
  have hT0b : (i₀ : ℤ) * (i₀ + 1) ≤ 21462 := by
    have : (0 : ℤ) ≤ i₀ := by positivity
    nlinarith
  have hMz : (M : ℤ) ≤ 3000 := by exact_mod_cast hM
  have hXM : X * M ≤ X * 3000 := by nlinarith
  have hv : (2 * X - 147) * (2 * X - 146) ≤ (i : ℤ) * (i + 1) := by
    have : 0 ≤ 2 * X - 147 := by linarith
    nlinarith
  nlinarith

/-! ## Lemma 15 -/

/-- The residues of `2^K` modulo 73 (the order of 2 modulo 73 is 9). -/
def pow2List : List ℕ := (List.range 9).map (fun k ↦ 2 ^ k % 73)

theorem two_pow_mod_73_mem (K : ℕ) : 2 ^ K % 73 ∈ pow2List := by
  have h : 2 ^ K % 73 = 2 ^ (K % 9) % 73 := by
    conv_lhs => rw [← Nat.mod_add_div K 9, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod (2 ^ 9)]
    norm_num
  rw [h, pow2List, List.mem_map]
  exact ⟨K % 9, List.mem_range.mpr (Nat.mod_lt _ (by norm_num)), rfl⟩

/-- A double class of pentagonal numbers: two `P_i`, `|i| ≤ 146`, in the class `c` modulo 73 and
distinct modulo `73^2`. -/
def DoubleClass1 (c : ℕ) : Prop :=
  ∃ i i' : ℤ, |i| ≤ 146 ∧ |i'| ≤ 146 ∧ pentagonal i % 73 = c ∧ pentagonal i' % 73 = c ∧
    pentagonal i % 5329 ≠ pentagonal i' % 5329

/-- A double class of triangular numbers `T_i = i(i+1)/2`, `i ≤ 146`. -/
def DoubleClass3 (c : ℕ) : Prop :=
  ∃ i i' : ℕ, i ≤ 146 ∧ i' ≤ 146 ∧ i * (i + 1) / 2 % 73 = c ∧ i' * (i' + 1) / 2 % 73 = c ∧
    i * (i + 1) / 2 % 5329 ≠ i' * (i' + 1) / 2 % 5329

/-- Condition (S) of Lemma 15 for `τ = 1`, in the reduced form of Remark 16(2)
(`μ = 3000`, `j = 12`, `M_min = 1`). -/
def CondS1 : Prop :=
  ∀ w < 4096, w % 2 = 1 → ∀ e ∈ pow2List, ∀ ρ < 73,
    ∃ M c, 1 ≤ M ∧ M ≤ 3000 ∧ coeff M (fbar ^ w) = 1 ∧ DoubleClass1 c ∧ (e * M + c) % 73 = ρ

/-- Condition (S) of Lemma 15 for `τ = 3` (`M_min = 3`). -/
def CondS3 : Prop :=
  ∀ w < 4096, w % 2 = 1 → ∀ e ∈ pow2List, ∀ ρ < 73,
    ∃ M c, 3 ≤ M ∧ M ≤ 3000 ∧ coeff M (fbar ^ w) = 1 ∧ DoubleClass3 c ∧ (e * M + c) % 73 = ρ

/-- Write `T = τ + 2^K w` with `K ≥ K₀` and `w` odd, for `T ≡ τ (mod 2^K₀)`, `T ≠ τ`. -/
theorem exists_two_pow_mul_odd_of_mod {τ K₀ T : ℕ} (hτ : τ < 2 ^ K₀) (hT : T % 2 ^ K₀ = τ)
    (hTτ : T ≠ τ) : ∃ K w, K₀ ≤ K ∧ w % 2 = 1 ∧ T = τ + 2 ^ K * w := by
  have hlt : τ < T := by
    have := Nat.mod_add_div T (2 ^ K₀)
    rcases Nat.eq_zero_or_pos (T / 2 ^ K₀) with h0 | h0
    · rw [h0, mul_zero, add_zero, hT] at this; omega
    · have := Nat.le_mul_of_pos_right (2 ^ K₀) h0; omega
  obtain ⟨K, m, hm, hD⟩ := Nat.exists_eq_two_pow_mul_odd (n := T - τ) (by omega)
  have hdvd : 2 ^ K₀ ∣ T - τ := by
    have := Nat.mod_add_div T (2 ^ K₀); rw [hT] at this
    exact ⟨T / 2 ^ K₀, by omega⟩
  have hK : K₀ ≤ K := by
    rw [hD] at hdvd
    have hcop : Nat.Coprime (2 ^ K₀) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hdvd)
  exact ⟨K, m, hK, Nat.odd_iff.mp hm, by omega⟩

/-- The value of `fbar ^ T` at a special index, `T = 1 + 2^K w`. -/
theorem coeff_special1 {K w M : ℕ} (hK : 13 ≤ K) (hM : M ≤ 3000) {j : ℤ} (hj : |j| ≤ 146) :
    coeff (2 ^ K * M + pentagonal j) (fbar ^ (1 + 2 ^ K * w)) = coeff M (fbar ^ w) := by
  classical
  set N := 2 ^ K * M + pentagonal j
  rw [coeff_fbar_pow_sparse, pow_one, Finset.sum_eq_single (pentagonal j)]
  · have hmem : pentagonal j ∈ Set.range pentagonal := ⟨j, rfl⟩
    rw [coeff_fbar, ite_eq_left hmem, one_mul, show N - pentagonal j = 2 ^ K * M by omega,
      ite_eq_left (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (Nat.two_pow_pos K)]
  · intro a ha hne
    rw [coeff_fbar]
    split_ifs with h1 h2
    · exfalso
      obtain ⟨z, rfl⟩ := h1
      have hle : pentagonal z ≤ 2 ^ K * M + pentagonal j := by
        have := Finset.mem_range.mp ha; omega
      have hdvd : (2 : ℤ) ^ K ∣ (pentagonal z : ℤ) - pentagonal j := by
        obtain ⟨q, hq⟩ := h2
        refine ⟨M - q, ?_⟩
        have : (N : ℤ) - pentagonal z = 2 ^ K * q := by
          rw [← Nat.cast_sub hle]; exact_mod_cast hq
        simp only [N] at this; push_cast at this; linarith
      exact hne (congrArg pentagonal (special_pent hK hj hM hle hdvd))
    all_goals simp
  · intro h; exfalso; apply h; rw [Finset.mem_range]; omega

open Classical in
theorem coeff_fbar_pow_three (a : ℕ) :
    coeff a (fbar ^ 3) = if ∃ k : ℕ, k * (k + 1) / 2 = a then 1 else 0 := by
  have h := jacobi_mod_two
  rw [fbar, f₁_eq_pentagonalSeries, h, coeff_mk]

/-- The value of `fbar ^ T` at a special index, `T = 3 + 2^K w`. -/
theorem coeff_special3 {K w M : ℕ} (hK : 11 ≤ K) (hM : M ≤ 3000) {j : ℕ} (hj : j ≤ 146) :
    coeff (2 ^ K * M + j * (j + 1) / 2) (fbar ^ (3 + 2 ^ K * w)) = coeff M (fbar ^ w) := by
  classical
  set N := 2 ^ K * M + j * (j + 1) / 2
  rw [coeff_fbar_pow_sparse, Finset.sum_eq_single (j * (j + 1) / 2)]
  · rw [coeff_fbar_pow_three, ite_eq_left ⟨j, rfl⟩, one_mul, show N - j * (j + 1) / 2 = 2 ^ K * M by omega,
      ite_eq_left (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (Nat.two_pow_pos K)]
  · intro a ha hne
    rw [coeff_fbar_pow_three]
    split_ifs with h1 h2
    · exfalso
      obtain ⟨k, rfl⟩ := h1
      have hle : k * (k + 1) / 2 ≤ 2 ^ K * M + j * (j + 1) / 2 := by
        have := Finset.mem_range.mp ha; omega
      have hdvd : (2 : ℤ) ^ K ∣ ((k * (k + 1) / 2 : ℕ) : ℤ) - ((j * (j + 1) / 2 : ℕ) : ℤ) := by
        obtain ⟨q, hq⟩ := h2
        refine ⟨M - q, ?_⟩
        have : (N : ℤ) - ((k * (k + 1) / 2 : ℕ) : ℤ) = 2 ^ K * q := by
          rw [← Nat.cast_sub hle]; exact_mod_cast hq
        simp only [N] at this; push_cast at this ⊢; linarith
      exact hne (by rw [special_tri hK hj hM hle hdvd])
    all_goals simp
  · intro h; exfalso; apply h; rw [Finset.mem_range]; omega

theorem mod_73_of_two_pow_mul (K M e c ρ : ℕ) (he : e = 2 ^ K % 73) (h : (e * M + c) % 73 = ρ)
    (P : ℕ) (hP : P % 73 = c) : (2 ^ K * M + P) % 73 = ρ := by
  have h1 : (2 ^ K * M) % 73 = (e * M) % 73 := by rw [he, Nat.mod_mul_mod]
  generalize 2 ^ K * M = Y at h1
  generalize e * M = Z at h1 h
  omega

/-- **The paper's Lemma 15** for `τ = 1` (`K₀ = 13`). -/
theorem closed_of_sparse1 (hS : CondS1) {T : ℕ} (hT : T % 2 ^ 13 = 1) (hT1 : T ≠ 1) :
    Closed (fbar ^ T) := by
  obtain ⟨K, w, hK, hw, rfl⟩ := exists_two_pow_mul_odd_of_mod (by norm_num) hT hT1
  intro ρ hρ
  obtain ⟨M, c, hM1, hM2, hcoef, ⟨i, i', hi, hi', hc, hc', hne⟩, hρ'⟩ :=
    hS (w % 4096) (Nat.mod_lt _ (by norm_num)) (by omega) _ (two_pow_mod_73_mem K) ρ hρ
  have hw' : coeff M (fbar ^ w) = 1 := by
    rw [coeff_fbar_pow_mod w 12 M (by omega)]; exact hcoef
  have hX : 8192 ≤ 2 ^ K * M := by
    have : 2 ^ 13 ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
    have := Nat.mul_le_mul this hM1; simpa using this
  refine ⟨2 ^ K * M + pentagonal i, 2 ^ K * M + pentagonal i', by omega, by omega,
    mod_73_of_two_pow_mul K M _ c ρ rfl hρ' _ hc, mod_73_of_two_pow_mul K M _ c ρ rfl hρ' _ hc',
    ?_, ?_, ?_⟩
  · generalize 2 ^ K * M = Y; omega
  · rw [coeff_special1 hK hM2 hi, hw']
  · rw [coeff_special1 hK hM2 hi', hw']

/-- **The paper's Lemma 15** for `τ = 3` (`K₀' = 11`). -/
theorem closed_of_sparse3 (hS : CondS3) {T : ℕ} (hT : T % 2 ^ 11 = 3) (hT3 : T ≠ 3) :
    Closed (fbar ^ T) := by
  obtain ⟨K, w, hK, hw, rfl⟩ := exists_two_pow_mul_odd_of_mod (by norm_num) hT hT3
  intro ρ hρ
  obtain ⟨M, c, hM1, hM2, hcoef, ⟨i, i', hi, hi', hc, hc', hne⟩, hρ'⟩ :=
    hS (w % 4096) (Nat.mod_lt _ (by norm_num)) (by omega) _ (two_pow_mod_73_mem K) ρ hρ
  have hw' : coeff M (fbar ^ w) = 1 := by
    rw [coeff_fbar_pow_mod w 12 M (by omega)]; exact hcoef
  have hX : 6144 ≤ 2 ^ K * M := by
    have : 2 ^ 11 ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
    have := Nat.mul_le_mul this hM1; simpa using this
  refine ⟨2 ^ K * M + i * (i + 1) / 2, 2 ^ K * M + i' * (i' + 1) / 2, by omega, by omega,
    mod_73_of_two_pow_mul K M _ c ρ rfl hρ' _ hc, mod_73_of_two_pow_mul K M _ c ρ rfl hρ' _ hc',
    ?_, ?_, ?_⟩
  · generalize 2 ^ K * M = Y; omega
  · rw [coeff_special3 hK hM2 hi, hw']
  · rw [coeff_special3 hK hM2 hi', hw']

end KeithZanello
