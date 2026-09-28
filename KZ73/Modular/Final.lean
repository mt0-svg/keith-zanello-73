import KZ73.Modular.SturmModTwo
import KZ73.Modular.Hecke
import KZ73.Main

/-!
# The modular step, unconditionally: the paper's Lemma 11 and the disproof of Conjecture B

`sturm_level_nine`: for every prime `p ≥ 5` and every `t ≥ 1`, if `heckeCoeff p t m` is even for
`1 ≤ m ≤ 4 t`, then it is even for every `m ≥ 1`. Proof: `W = H₀ L + L²` is a modular form of
weight 4 on `Γ₀(9)` with integer coefficients and `W ≡ η(24z) (mod 2)` (`red2_wz`); the Hecke
operator `T_p` (`p ∤ 9`) maps `W^t` to a form of weight `4 t` on `Γ₀(9)` whose coefficients are
`heckeCoeff p t m` modulo 2 (`p^(4t-1)` is odd) and whose constant term is 0; Sturm's theorem
modulo 2 on `Γ₀(9)` (`sturm_mod_two`, bound `4 t`) concludes.

Consequences: `sturmHypothesis_proved : SturmHypothesis` (the paper's Lemma 11, bound
`48 (t + 1) ≥ 4 t`), `hecke73_proved : Hecke73`, `theorem1 : Theorem1` and
`conjectureB_false : ¬ ConjectureB`.
-/

open UpperHalfPlane PowerSeries

namespace KeithZanello

namespace Modular

theorem zmod_two_of_odd {p : ℕ} (hp : Odd p) (e : ℕ) : ((p : ℤ) : ZMod 2) ^ e = 1 := by
  rw [Int.cast_natCast, (ZMod.natCast_eq_one_iff_odd).mpr hp, one_pow]

/-- **Lemma 11 at level 9**: Sturm's bound `4 t` for `T_p η(24z)^t` modulo 2. -/
theorem sturm_level_nine (p t : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (ht : 1 ≤ t)
    (hsmall : ∀ m, 1 ≤ m → m ≤ 4 * t → Even (heckeCoeff p t m)) :
    ∀ m, 1 ≤ m → Even (heckeCoeff p t m) := by
  obtain ⟨H, hH⟩ := exists_H0'
  obtain ⟨L, hL⟩ := exists_L
  have hW : HasIntQExp (H.mul L + L.mul L) wz := by
    have := (hH.mul hL).add (hL.mul hL)
    rwa [← sq] at this
  have hWt := hW.pow t
  have hpN : ¬ p ∣ 9 := by
    intro h
    have h3 : p ∣ 3 ^ 2 := by norm_num; exact h
    have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
    omega
  obtain ⟨g, hg⟩ := exists_heckeT_Gamma0 ((H.mul L + L.mul L).pow t) hp hpN
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  set e := 4 * t - 1 with he
  /- the integer expansion of `T_p W^t` -/
  set Q : ℤ⟦X⟧ := PowerSeries.mk fun n ↦
    coeff (n * p) (wz ^ t) + if p ∣ n then (p : ℤ) ^ e * coeff (n / p) (wz ^ t) else 0 with hQ
  have hk : ((t : ℤ) * (2 + 2)) - 1 = ((e : ℕ) : ℤ) := by rw [he]; push_cast; omega
  have hgQ : HasIntQExp g Q := by
    intro n
    rw [hg, hWt, hQ, coeff_mk]
    split_ifs
    · rw [hWt, hk, zpow_natCast]; push_cast; ring
    · simp
  /- modulo 2, the coefficients of `Q` are the `heckeCoeff p t n` -/
  have hmod : ∀ n, ((coeff n Q : ℤ) : ZMod 2) = ((heckeCoeff p t n : ℤ) : ZMod 2) := by
    intro n
    rw [hQ, coeff_mk, heckeCoeff, Int.cast_add, Int.cast_add, coeff_wz_pow_zmod_two, mul_comm n p]
    congr 1
    split_ifs
    · rw [Int.cast_mul, Int.cast_pow, zmod_two_of_odd hpodd, one_mul, coeff_wz_pow_zmod_two]
    · rfl
  have hQ0 : coeff 0 Q = 0 := by
    have h0 : coeff 0 (wz ^ t) = 0 := by
      rw [coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply,
        coeff_zero_wz, zero_pow (by omega)]
    rw [hQ, coeff_mk, zero_mul, h0, zero_add, ite_eq_left (dvd_zero p), Nat.zero_div, h0, mul_zero]
  have hw : (t : ℤ) * (2 + 2) = ((2 * (2 * t) : ℕ) : ℤ) := by push_cast; ring
  have hall := sturm_mod_two (2 * t) (g.mcast hw) Q (hgQ.mcast hw) fun n hn ↦ by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [hQ0]; exact dvd_zero 2
    · rw [← even_iff_two_dvd, even_iff_zmod, hmod, ← even_iff_zmod]
      exact hsmall n hpos (by omega)
  intro m _
  rw [even_iff_zmod, ← hmod, ← even_iff_zmod, even_iff_two_dvd]
  exact hall m

end Modular

/-- **The paper's Lemma 11**, proved (`SturmHypothesis` is no longer a hypothesis). -/
theorem sturmHypothesis_proved : SturmHypothesis :=
  fun p t hp hp5 hodd hsmall ↦ Modular.sturm_level_nine p t hp hp5 hodd.pos
    fun m h1 h2 ↦ hsmall m h1 (by omega)

/-- `T_73 H_t ≡ 0 (mod 2)` for the eighteen elements `t ≥ 5` of `E73`. -/
theorem hecke73_proved : Hecke73 :=
  hecke73_of_sturmHypothesis73 (sturmHypothesis73_of_sturmHypothesis sturmHypothesis_proved)

/-- **The paper's Theorem 1**: for odd `t`, `f₁^t` is `73²`-even exactly when `t ∈ E73`, with the
base `222 t mod 73²`, unique for `t ≥ 5`. -/
theorem theorem1 : Theorem1 := mainClaim sturmHypothesis_proved

/-- **Keith and Zanello's Conjecture B is false** (it fails at `p = 73`). -/
theorem conjectureB_false : ¬ ConjectureB := not_conjectureB sturmHypothesis_proved

end KeithZanello
