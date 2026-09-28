import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Coefficients of three weight 2 Eisenstein series on `Γ₀(9)`

With `σ = σ₁`:

* `h0Coeff`: `H₀ = (3 E₂(3z) - E₂(z)) / 2 = 1 + 12 ∑ (σ(n) - 3 σ(n/3)) qⁿ` (second term when `3 ∣ n`);
* `m1Coeff`: `M₁ = ∑_{n ≡ 1 (3)} σ(n) qⁿ`;
* `m2Coeff`: `M₂ = ∑_{n ≡ 2 (3)} σ(n) qⁿ`.

`KZ73/Modular/Eisenstein.lean` shows that these are the `q`-expansions of modular forms of weight
2 on `Γ₀(9)`.
-/

open scoped ArithmeticFunction.sigma

namespace KeithZanello.Modular

/-- Coefficients of `H₀ = (3 E₂(3z) - E₂(z)) / 2`. -/
def h0Coeff (n : ℕ) : ℤ :=
  if n = 0 then 1 else 12 * ((σ 1 n : ℤ) - 3 * (if 3 ∣ n then (σ 1 (n / 3) : ℤ) else 0))

/-- Coefficients of `M₁ = ∑_{n ≡ 1 (mod 3)} σ₁(n) qⁿ`. -/
def m1Coeff (n : ℕ) : ℤ := if n % 3 = 1 then (σ 1 n : ℤ) else 0

/-- Coefficients of `M₂ = ∑_{n ≡ 2 (mod 3)} σ₁(n) qⁿ`. -/
def m2Coeff (n : ℕ) : ℤ := if n % 3 = 2 then (σ 1 n : ℤ) else 0

end KeithZanello.Modular
