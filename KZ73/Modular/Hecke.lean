import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import KZ73.Modular.P2M.HeckeQExp
import KZ73.Modular.P2M.HeckeSlash
import KZ73.Modular.P2M.HeckeCusp

/-!
# The Hecke operator `T_p` on `M_k(Γ₀(N))` and its action on `q`-expansions

For a prime `p ∤ N` and `f ∈ M_k(Γ₀(N))`, `T_p f ∈ M_k(Γ₀(N))` and
`a_n(T_p f) = a_{np}(f) + [p ∣ n] p^{k-1} a_{n/p}(f)`.

The operator and its properties are ported from the Prove2Me proof repository (see
`KZ73/Modular/P2M/`); the modular form below is assembled as in its
`CuspForm.exists_coe_eq_heckeT` (`P2M/Sol/S_CuspForm_exists_coe_eq_heckeT.lean`), with boundedness at the cusps in place of vanishing.
-/

open UpperHalfPlane

namespace KeithZanello.Modular

theorem exists_heckeT_Gamma0 {N : ℕ} {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 N) k, ∀ n : ℕ,
      (qExpansion 1 g).coeff n = (qExpansion 1 f).coeff (n * p) +
        if p ∣ n then (p : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff (n / p) else 0 := by
  have : NeZero N := ⟨fun h => hpN (h ▸ dvd_zero p)⟩
  let g : ModularForm (CongruenceSubgroup.Gamma0 N) k :=
    { toFun := P2M.heckeT k p ⇑f
      slash_action_eq' := fun γ hγ => P2M.heckeT_slash_eq_self_of_mem_Gamma0 k hp hpN
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
      holo' := P2M.mdifferentiable_heckeT k p (ModularFormClass.holo f)
      bdd_at_cusps' := fun hc => P2M.isBoundedAt_heckeT f p hc }
  have hg : ⇑g = P2M.heckeT k p ⇑f := rfl
  have h1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [CongruenceSubgroup.strictPeriods_Gamma0]
  refine ⟨g, fun n => ?_⟩
  have := P2M.qCoeff_heckeT hp.ne_zero f h1 n
  rw [P2M.qCoeff, P2M.coeffHeckeT_apply, ← hg] at this
  exact this

end KeithZanello.Modular
