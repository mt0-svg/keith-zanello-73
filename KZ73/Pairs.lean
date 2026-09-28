import KZ73.Bits

/-!
# Pair certificates at `p = 73`

A pair for `ψ ∈ (ZMod 2)⟦X⟧` in the class `ρ` modulo `73` is two indices `N₁, N₂ ≥ 73^2`, both
`≡ ρ (mod 73)`, distinct modulo `73^2`, where `ψ` has coefficient `1` (the paper's Definition 6).
A pair for `fbar ^ t` in the class `r mod 73` excludes the base `r` (Lemma 7). The base
`r_t = 222 t mod 73^2` collects the indices `N` with `73 ∥ 24 N + t` (Lemma 9), and a good `t`
isolated by pairs in the other classes is the only good exponent in a whole binary ball
(Lemma 13).
-/

open PowerSeries

namespace KeithZanello

/-- The base `r_t` at `p = 73`: `-t / 24 mod 73^2`, since `24 * 222 = 73^2 - 1`. -/
def rt (t : ℕ) : ℕ := 222 * t % 5329

/-- A pair for `ψ` in the class `ρ` modulo `73`. -/
def IsPair (ψ : (ZMod 2)⟦X⟧) (ρ N₁ N₂ : ℕ) : Prop :=
  5329 ≤ N₁ ∧ 5329 ≤ N₂ ∧ N₁ % 73 = ρ ∧ N₂ % 73 = ρ ∧ N₁ % 5329 ≠ N₂ % 5329 ∧
    coeff N₁ ψ = 1 ∧ coeff N₂ ψ = 1

def HasPair (ψ : (ZMod 2)⟦X⟧) (ρ : ℕ) : Prop := ∃ N₁ N₂, IsPair ψ ρ N₁ N₂

/-- `ψ` has a pair in every class modulo `73`. -/
def Closed (ψ : (ZMod 2)⟦X⟧) : Prop := ∀ ρ < 73, HasPair ψ ρ

theorem pow_two_73 : (73 : ℕ) ^ 2 = 5329 := by norm_num

/-- One odd coefficient at `N ≥ 73^2`, `N ≡ r (mod 73)`, `N ≢ r (mod 73^2)` excludes the base `r`
(proof of the paper's Lemma 7). -/
theorem not_evenWithBase_of_index {t r N : ℕ} (hr : r < 5329) (hN : 5329 ≤ N)
    (hNr : N % 73 = r % 73) (hNr' : N % 5329 ≠ r) (hc : coeff N (fbar ^ t) = 1) :
    ¬ IsEvenWithBase 73 t r := by
  intro h
  have h1 := h ((N - r) / 5329) ((N - r) / 73 % 73) (by omega) (by omega)
  have hN' : 73 ^ 2 * ((N - r) / 5329) + (N - r) / 73 % 73 * 73 + r = N := by
    rw [pow_two_73]; omega
  rw [hN'] at h1
  exact (not_even_c_iff t N).mpr hc h1

/-- **The paper's Lemma 7.** -/
theorem not_evenWithBase_of_hasPair {t r : ℕ} (hr : r < 5329) (h : HasPair (fbar ^ t) (r % 73)) :
    ¬ IsEvenWithBase 73 t r := by
  obtain ⟨N₁, N₂, h1, h2, h3, h4, h5, h6, h7⟩ := h
  by_cases hN : N₁ % 5329 = r
  · exact not_evenWithBase_of_index hr h2 h4 (by omega) h7
  · exact not_evenWithBase_of_index hr h1 h3 hN h6

theorem not_isP2Even_of_closed {t : ℕ} (h : Closed (fbar ^ t)) : ¬ IsP2Even 73 t := by
  rintro ⟨r, hr, hb⟩
  rw [pow_two_73] at hr
  exact not_evenWithBase_of_hasPair hr (h (r % 73) (Nat.mod_lt _ (by norm_num))) hb

/-- **The paper's Lemma 9** at `p = 73`. -/
theorem index_iff (t N : ℕ) :
    (73 ∣ 24 * N + t ∧ ¬ 5329 ∣ 24 * N + t) ↔ (N % 73 = rt t % 73 ∧ N % 5329 ≠ rt t) := by
  unfold rt; omega

theorem evenWithBase_rt_of_condG {t : ℕ} (hG : CondG 73 t) : IsEvenWithBase 73 t (rt t) := by
  intro n k hk1 hk2
  apply hG
  · rw [pow_two_73]; unfold rt; omega
  · rw [pow_two_73]; unfold rt; omega

theorem coeff_eq_zero_of_condG {t N : ℕ} (hG : CondG 73 t) (h1 : N % 73 = rt t % 73)
    (h2 : N % 5329 ≠ rt t) : coeff N (fbar ^ t) = 0 := by
  rw [← even_c_iff]
  have := (index_iff t N).mpr ⟨h1, h2⟩
  exact hG N this.1 (by rw [pow_two_73]; exact this.2)

/-! ## The paper's Lemma 13 -/

section Centre

variable {t h : ℕ}

/-- Hypothesis (i) of Lemma 13: pairs below `2^h` in every class other than that of `r_t`. -/
def CentreI (t h : ℕ) : Prop :=
  ∀ ρ < 73, ρ ≠ rt t % 73 → ∃ N₁ N₂, N₁ < 2 ^ h ∧ N₂ < 2 ^ h ∧ IsPair (fbar ^ t) ρ N₁ N₂

/-- Hypothesis (ii) of Lemma 13: an odd coefficient below `2^h` in the class of `r_t`. -/
def CentreII (t h : ℕ) : Prop :=
  ∃ Na, 5329 ≤ Na ∧ Na < 2 ^ h ∧ Na % 73 = rt t % 73 ∧ coeff Na (fbar ^ t) = 1

theorem two_pow_mod_73_ne_zero (K : ℕ) : 2 ^ K % 73 ≠ 0 := by
  intro h
  have : (73 : ℕ) ∣ 2 ^ K := Nat.dvd_of_mod_eq_zero h
  have := (Nat.prime_dvd_prime_iff_eq (by decide) Nat.prime_two).mp
    ((by decide : Nat.Prime 73).dvd_of_dvd_pow this)
  omega

/-- **The paper's Lemma 13**, second part: every `T ≡ t (mod 2^h)` other than `t` is closed. -/
theorem closed_of_centre (ht : t < 2 ^ h) (hG : CondG 73 t) (hi : CentreI t h)
    (hii : CentreII t h) {T : ℕ} (hT : T % 2 ^ h = t) (hTt : T ≠ t) : Closed (fbar ^ T) := by
  -- write `T = t + 2^K (2j + 1)` with `K ≥ h`
  have hTt' : t < T := by
    have := Nat.mod_add_div T (2 ^ h)
    rcases Nat.eq_zero_or_pos (T / 2 ^ h) with h0 | h0
    · rw [h0, mul_zero, add_zero, hT] at this; omega
    · have := Nat.le_mul_of_pos_right (2 ^ h) h0; omega
  obtain ⟨K, m, hm, hD⟩ := Nat.exists_eq_two_pow_mul_odd (n := T - t) (by omega)
  have hdvd : 2 ^ h ∣ T - t := by
    have := Nat.mod_add_div T (2 ^ h); rw [hT] at this
    exact ⟨T / 2 ^ h, by omega⟩
  have hKh : h ≤ K := by
    rw [hD] at hdvd
    have hcop : Nat.Coprime (2 ^ h) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hdvd)
  obtain ⟨j, rfl⟩ := hm
  have hTeq : T = t + 2 ^ K * (2 * j + 1) := by omega
  subst hTeq
  set X := 2 ^ K with hX
  have hhX : 2 ^ h ≤ X := Nat.pow_le_pow_right (by norm_num) hKh
  have hX73 : X % 73 ≠ 0 := two_pow_mod_73_ne_zero K
  have hK1 : 2 ^ (K + 1) = 2 * X := by rw [pow_succ]; ring
  have hcoeff := fun N (hN : N < 2 * X) ↦ coeff_fbar_pow_centre t K j N (hK1 ▸ hN)
  intro ρ hρ
  by_cases hρt : ρ = rt t % 73
  · -- the class of `r_t`
    obtain ⟨Na, hNa1, hNa2, hNa3, hNa4⟩ := hii
    have hNa5 : Na % 5329 = rt t := by
      by_contra hne
      have := coeff_eq_zero_of_condG hG hNa3 hne
      rw [hNa4] at this; exact one_ne_zero this
    set ρ' := (rt t % 73 + 73 - X % 73) % 73 with hρ'
    obtain ⟨N₁, N₂, hN₁, hN₂, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ :=
      hi ρ' (Nat.mod_lt _ (by norm_num)) (by omega)
    -- choose the index `N'` of the pair with `N' + X ≢ r_t (mod 73^2)`
    obtain ⟨N', hN'1, hN'2, hN'3, hN'4, hN'5⟩ : ∃ N', N' < 2 ^ h ∧ 5329 ≤ N' ∧ N' % 73 = ρ' ∧
        (N' + X) % 5329 ≠ rt t ∧ coeff N' (fbar ^ t) = 1 := by
      by_cases hc : (N₁ + X) % 5329 = rt t
      · exact ⟨N₂, hN₂, hp2, hp4, by omega, hp7⟩
      · exact ⟨N₁, hN₁, hp1, hp3, hc, hp6⟩
    have hNb0 : coeff (N' + X) (fbar ^ t) = 0 :=
      coeff_eq_zero_of_condG hG (by omega) hN'4
    refine ⟨Na, N' + X, hNa1, by omega, by omega, by omega, by omega, ?_, ?_⟩
    · rw [hcoeff Na (by omega), ite_eq_right (by omega), add_zero, hNa4]
    · rw [hcoeff (N' + X) (by omega), ite_eq_left (by omega), Nat.add_sub_cancel, hNb0, hN'5,
        zero_add]
  · obtain ⟨N₁, N₂, hN₁, hN₂, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hi ρ hρ hρt
    refine ⟨N₁, N₂, hp1, hp2, hp3, hp4, hp5, ?_, ?_⟩
    · rw [hcoeff N₁ (by omega), ite_eq_right (by omega), add_zero, hp6]
    · rw [hcoeff N₂ (by omega), ite_eq_right (by omega), add_zero, hp7]

/-- **The paper's Lemma 13**, first part: under (i) and (ii), a base must be `Na mod 73^2`. -/
theorem base_eq_of_centre (hi : CentreI t h) {Na : ℕ} (hNa1 : 5329 ≤ Na)
    (hNa3 : Na % 73 = rt t % 73) (hNa4 : coeff Na (fbar ^ t) = 1) {r : ℕ} (hr : r < 5329)
    (hb : IsEvenWithBase 73 t r) : r = Na % 5329 := by
  have hρ : r % 73 = rt t % 73 := by
    by_contra hne
    obtain ⟨N₁, N₂, -, -, hp⟩ := hi (r % 73) (Nat.mod_lt _ (by norm_num)) hne
    exact not_evenWithBase_of_hasPair hr ⟨N₁, N₂, hp⟩ hb
  by_contra hne
  exact not_evenWithBase_of_index hr hNa1 (by omega) (Ne.symm hne) hNa4 hb

end Centre

/-! ## Bit-level pair tests -/

/-- Residues modulo `73^2` of the set bits of `B` at the positions `5329 j + a`, `1 ≤ j ≤ J`. -/
def foldRes (B : ℕ) : ℕ → ℕ
  | 0 => 0
  | J + 1 => ((B >>> (5329 * (J + 1))) &&& mask 5329) ||| foldRes B J

theorem testBit_foldRes (B J a : ℕ) (h : (foldRes B J).testBit a = true) :
    a < 5329 ∧ ∃ j, 1 ≤ j ∧ B.testBit (5329 * j + a) = true := by
  induction J with
  | zero => simp [foldRes] at h
  | succ J ih =>
    rw [foldRes, Nat.testBit_lor, Nat.testBit_land, Nat.testBit_shiftRight, testBit_mask,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨h2, J + 1, by omega, h1⟩
    · exact ih h

/-- One step of `twice`: fold in the chunk number `n` (width 73) of `R`. -/
def twiceStep (R n : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  ((s.1 ||| ((R >>> (73 * n)) &&& mask 73)), (s.2 ||| (s.1 &&& ((R >>> (73 * n)) &&& mask 73))))

/-- Classes `ρ < 73` seen in at least one (first component) or at least two (second component)
of the chunks `0, …, n-1` of width 73 of `R`. -/
def twice (R : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 => twiceStep R n (twice R n)

theorem testBit_twice (R n ρ : ℕ) :
    ((twice R n).1.testBit ρ = true → ∃ b < n, R.testBit (73 * b + ρ) = true) ∧
    ((twice R n).2.testBit ρ = true → ∃ b₁ b₂, b₁ < b₂ ∧ b₂ < n ∧
      R.testBit (73 * b₁ + ρ) = true ∧ R.testBit (73 * b₂ + ρ) = true) := by
  induction n with
  | zero => simp [twice]
  | succ n ih =>
    simp only [twice, twiceStep, Nat.testBit_lor, Nat.testBit_land, Nat.testBit_shiftRight,
      testBit_mask, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · rintro (h | ⟨h, -⟩)
      · obtain ⟨b, hb, hb'⟩ := ih.1 h; exact ⟨b, by omega, hb'⟩
      · exact ⟨n, by omega, h⟩
    · rintro (h | ⟨h1, h2, -⟩)
      · obtain ⟨b₁, b₂, h12, h2n, hb1, hb2⟩ := ih.2 h
        exact ⟨b₁, b₂, h12, by omega, hb1, hb2⟩
      · obtain ⟨b, hb, hb'⟩ := ih.1 h1
        exact ⟨b, n, hb, by omega, hb', h2⟩

/-- The two class masks of `B` (positions `≥ 73^2`, below `L`). -/
def classMasks (B L : ℕ) : ℕ × ℕ := twice (foldRes B (L / 5329)) 73

theorem pair_of_classMasks {B L : ℕ} {ψ : (ZMod 2)⟦X⟧} (hB : Rep B L ψ) {ρ : ℕ} (hρ : ρ < 73)
    (h : (classMasks B L).2.testBit ρ = true) :
    ∃ N₁ N₂, N₁ < L ∧ N₂ < L ∧ IsPair ψ ρ N₁ N₂ := by
  obtain ⟨b₁, b₂, h12, h2n, hb1, hb2⟩ := (testBit_twice _ _ ρ).2 h
  obtain ⟨-, j₁, hj₁, hB1⟩ := testBit_foldRes B _ _ hb1
  obtain ⟨-, j₂, hj₂, hB2⟩ := testBit_foldRes B _ _ hb2
  have hL1 : 5329 * j₁ + (73 * b₁ + ρ) < L := by
    by_contra hc; rw [hB.testBit_ge (by omega)] at hB1; exact absurd hB1 (by decide)
  have hL2 : 5329 * j₂ + (73 * b₂ + ρ) < L := by
    by_contra hc; rw [hB.testBit_ge (by omega)] at hB2; exact absurd hB2 (by decide)
  refine ⟨_, _, hL1, hL2, by omega, by omega, by omega, by omega, by omega,
    (hB.coeff_eq_one_iff hL1).mpr hB1, (hB.coeff_eq_one_iff hL2).mpr hB2⟩

theorem one_of_classMasks {B L : ℕ} {ψ : (ZMod 2)⟦X⟧} (hB : Rep B L ψ) {ρ : ℕ} (hρ : ρ < 73)
    (h : (classMasks B L).1.testBit ρ = true) :
    ∃ N, 5329 ≤ N ∧ N < L ∧ N % 73 = ρ ∧ coeff N ψ = 1 := by
  obtain ⟨b, hb, hb'⟩ := (testBit_twice _ _ ρ).1 h
  obtain ⟨-, j, hj, hB1⟩ := testBit_foldRes B _ _ hb'
  have hL : 5329 * j + (73 * b + ρ) < L := by
    by_contra hc; rw [hB.testBit_ge (by omega)] at hB1; exact absurd hB1 (by decide)
  exact ⟨_, by omega, hL, by omega, (hB.coeff_eq_one_iff hL).mpr hB1⟩

/-- The closure test: a pair in every class. -/
def closedTest (B L : ℕ) : Bool := (classMasks B L).2 == mask 73

/-- The centre test for `t`: conditions (i) and (ii) of Lemma 13. -/
def centreTest (t B L : ℕ) : Bool :=
  (((classMasks B L).2 ||| 2 ^ (rt t % 73)) == mask 73) && (classMasks B L).1.testBit (rt t % 73)

theorem closed_of_closedTest {B L : ℕ} {ψ : (ZMod 2)⟦X⟧} (hB : Rep B L ψ)
    (h : closedTest B L = true) : Closed ψ := by
  intro ρ hρ
  have h' : (classMasks B L).2 = mask 73 := by simpa [closedTest] using h
  obtain ⟨N₁, N₂, -, -, hp⟩ := pair_of_classMasks hB hρ (by rw [h', testBit_mask]; simpa)
  exact ⟨N₁, N₂, hp⟩

theorem centre_of_centreTest {t B h : ℕ} (hB : Rep B (2 ^ h) (fbar ^ t))
    (hc : centreTest t B (2 ^ h) = true) : CentreI t h ∧ CentreII t h := by
  simp only [centreTest, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨h1, h2⟩ := hc
  have hr : rt t % 73 < 73 := Nat.mod_lt _ (by norm_num)
  refine ⟨fun ρ hρ hne ↦ pair_of_classMasks hB hρ ?_, one_of_classMasks hB hr h2⟩
  have := congrArg (fun x ↦ x.testBit ρ) h1
  simp only [Nat.testBit_lor, Nat.testBit_two_pow, testBit_mask] at this
  simpa [hρ, Ne.symm hne] using this

end KeithZanello
