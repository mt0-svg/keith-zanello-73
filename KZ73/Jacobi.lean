import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination

/-!
# Jacobi's identity for the cube of Euler's product

Main results, all proved, no `sorry`:

* `KeithZanello.jacobi_mod_two`: `f₁^3 ≡ ∑_{k ≥ 0} q^(k(k+1)/2) (mod 2)`, where
  `f₁ = pentagonalSeries ℤ = ∏_{n ≥ 1} (1 - q^n)`.
* `KeithZanello.pentagonalSeries_pow_three_eq`: the full identity
  `f₁^3 = ∑_{k ≥ 0} (-1)^k (2k+1) q^(k(k+1)/2)` over any commutative ring, coefficientwise;
  `KeithZanello.coeff_pentagonalSeries_pow_three` gives the coefficient at `k(k+1)/2`.

Proof (finite, polynomial algebra only):
1. Gaussian binomials `gauss q N m` over a commutative ring, from the Pascal rule
   `[N+1, m+1] = [N, m] + q^(m+1) [N, m+1]`; the ratio identity, the second Pascal rule, the
   two-step rule for `[N+2, m]`, and the product relation `[N, m] (q;q)_m (q;q)_(N-m) = (q;q)_N`.
2. Finite Jacobi triple product (`coeff_jtp`): the coefficient of `x^m` in
   `∏_{i<n} (1 + x q^(i+1)) (x + q^i)` is `[2n, m] q^(T(m-n))`, with `T(j) = j(j+1)/2` and
   `T(-j) = T(j-1)`.
3. Derivative in `x` at `x = -1` (`jtp_deriv`): the factor `x + 1` kills every other term, so
   `(-1)^(n+1) (q;q)_(n+1) (q;q)_n = ∑_m m (-1)^m [2n+2, m] q^(T(m-n-1))`.
4. Limit in `R⟦X⟧`: `[M, m] f₁ ≡ 1` modulo `X^(min(m, M-m)+1)` by the product relation, so the
   right side times `f₁` is `∑_m m (-1)^m q^(T(m-N))` modulo `X^N`; pairing `m` with
   `2N - 1 - m` turns it into `(-1)^N ∑_{j<N} (-1)^j (2j+1) q^(T(j)) + 2N q^(T(N))`, while the
   left side times `f₁` is `(-1)^N f₁^3` modulo `X^N`.
-/

namespace KeithZanello

namespace Jacobi

/-! ## Gaussian binomial coefficients -/

section Gauss

variable {A : Type*} [CommRing A]

/-- The Gaussian binomial coefficient `[N choose m]` evaluated at `q`, defined by the Pascal rule
`[N+1, m+1] = [N, m] + q^(m+1) [N, m+1]`. -/
def gauss (q : A) : ℕ → ℕ → A
  | _, 0 => 1
  | 0, _ + 1 => 0
  | N + 1, m + 1 => gauss q N m + q ^ (m + 1) * gauss q N (m + 1)

@[simp] lemma gauss_zero_right (q : A) (N : ℕ) : gauss q N 0 = 1 := by
  cases N <;> rfl

@[simp] lemma gauss_zero_succ (q : A) (m : ℕ) : gauss q 0 (m + 1) = 0 := rfl

lemma gauss_succ_succ (q : A) (N m : ℕ) :
    gauss q (N + 1) (m + 1) = gauss q N m + q ^ (m + 1) * gauss q N (m + 1) := rfl

lemma gauss_eq_zero_of_lt (q : A) : ∀ {N m : ℕ}, N < m → gauss q N m = 0
  | 0, _ + 1, _ => rfl
  | N + 1, m + 1, h => by
      rw [gauss_succ_succ, gauss_eq_zero_of_lt q (by omega), gauss_eq_zero_of_lt q (by omega)]
      simp

lemma gauss_self (q : A) : ∀ N : ℕ, gauss q N N = 1
  | 0 => rfl
  | N + 1 => by rw [gauss_succ_succ, gauss_self q N, gauss_eq_zero_of_lt q (by omega)]; simp

/-- Ratio identity `(1 - q^(m+1)) [N, m+1] = (1 - q^(N-m)) [N, m]` (truncated subtraction). -/
lemma gauss_ratio (q : A) : ∀ N m : ℕ,
    (1 - q ^ (m + 1)) * gauss q N (m + 1) = (1 - q ^ (N - m)) * gauss q N m
  | 0, 0 => by simp
  | 0, m + 1 => by simp
  | N + 1, 0 => by
      have h := gauss_ratio q N 0
      simp only [gauss_zero_right, Nat.sub_zero, zero_add, pow_one, mul_one] at h ⊢
      rw [show (1 : ℕ) = 0 + 1 from rfl, gauss_succ_succ, gauss_zero_right]
      linear_combination q * h
  | N + 1, m + 1 => by
      have h1 := gauss_ratio q N (m + 1)
      have h0 := gauss_ratio q N m
      rw [gauss_succ_succ q N (m + 1), gauss_succ_succ q N m,
        show N + 1 - (m + 1) = N - m by omega]
      rcases Nat.lt_or_ge N (m + 1) with hlt | hle
      · rw [gauss_eq_zero_of_lt q hlt, gauss_eq_zero_of_lt q (by omega : N < m + 1 + 1)]
        rcases Nat.lt_or_ge N m with h2 | h2
        · rw [gauss_eq_zero_of_lt q h2]; ring
        · rw [show N - m = 0 by omega]; ring
      · have e1 : q ^ (m + 1 + 1) * q ^ (N - (m + 1)) = q ^ (N + 1) := by
          rw [← pow_add]; congr 1; omega
        have e2 : q ^ (N - m) * q ^ (m + 1) = q ^ (N + 1) := by
          rw [← pow_add]; congr 1; omega
        linear_combination q ^ (m + 1 + 1) * h1 + h0 - gauss q N (m + 1) * e1 +
          gauss q N (m + 1) * e2

/-- Second Pascal rule `[N+1, m+1] = q^(N-m) [N, m] + [N, m+1]` (truncated subtraction). -/
lemma gauss_succ_succ' (q : A) (N m : ℕ) :
    gauss q (N + 1) (m + 1) = q ^ (N - m) * gauss q N m + gauss q N (m + 1) := by
  rw [gauss_succ_succ]
  linear_combination (-1 : A) * gauss_ratio q N m

/-- Two-step rule at index `1`. -/
lemma gauss_two_step_one (q : A) (N : ℕ) :
    gauss q (N + 2) 1 = q * gauss q N 1 + (1 + q ^ (N + 1)) * gauss q N 0 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, gauss_succ_succ' q (N + 1) 0, gauss_succ_succ q N 0]
  simp only [gauss_zero_right, Nat.sub_zero, zero_add, pow_one]
  ring

/-- Two-step rule
`[N+2, m+2] = q^(m+2) [N, m+2] + (1 + q^(N+1)) [N, m+1] + q^(N-m) [N, m]`. -/
lemma gauss_two_step (q : A) (N m : ℕ) :
    gauss q (N + 2) (m + 2) = q ^ (m + 2) * gauss q N (m + 2) +
      (1 + q ^ (N + 1)) * gauss q N (m + 1) + q ^ (N - m) * gauss q N m := by
  rw [show N + 2 = (N + 1) + 1 from rfl, show m + 2 = (m + 1) + 1 from rfl,
    gauss_succ_succ' q (N + 1) (m + 1), gauss_succ_succ q N m, gauss_succ_succ q N (m + 1),
    show N + 1 - (m + 1) = N - m by omega]
  rcases Nat.lt_or_ge N (m + 1) with hlt | hle
  · rw [gauss_eq_zero_of_lt q hlt, gauss_eq_zero_of_lt q (by omega : N < m + 1 + 1)]
    ring
  · have e : q ^ (N - m) * q ^ (m + 1) = q ^ (N + 1) := by
      rw [← pow_add]; congr 1; omega
    linear_combination gauss q N (m + 1) * e

/-- `(q; q)_j = ∏_{i < j} (1 - q^(i+1))`. -/
def qp (q : A) (j : ℕ) : A := ∏ i ∈ Finset.range j, (1 - q ^ (i + 1))

@[simp] lemma qp_zero (q : A) : qp q 0 = 1 := by simp [qp]

lemma qp_succ (q : A) (j : ℕ) : qp q (j + 1) = qp q j * (1 - q ^ (j + 1)) := by
  simp [qp, Finset.prod_range_succ]

/-- Product relation `[N, m] (q;q)_m (q;q)_(N-m) = (q;q)_N` for `m ≤ N`. -/
lemma gauss_mul_qp (q : A) : ∀ N m : ℕ, m ≤ N → gauss q N m * qp q m * qp q (N - m) = qp q N
  | 0, 0, _ => by simp
  | N + 1, 0, _ => by simp
  | N + 1, m + 1, h => by
      have h0 := gauss_mul_qp q N m (by omega)
      rw [gauss_succ_succ, show N + 1 - (m + 1) = N - m by omega, qp_succ q m, qp_succ q N]
      rcases Nat.lt_or_ge m N with hlt | hge
      · have h1 := gauss_mul_qp q N (m + 1) hlt
        rw [qp_succ q m] at h1
        rw [show N - m = (N - (m + 1)) + 1 by omega, qp_succ q (N - (m + 1))] at *
        have e : q ^ (m + 1) * q ^ (N - (m + 1) + 1) = q ^ (N + 1) := by
          rw [← pow_add]; congr 1; omega
        linear_combination (1 - q ^ (m + 1)) * h0 +
          q ^ (m + 1) * (1 - q ^ (N - (m + 1) + 1)) * h1 - qp q N * e
      · have hm : m = N := by omega
        subst hm
        rw [gauss_self, gauss_eq_zero_of_lt q (by omega), Nat.sub_self, qp_zero]
        ring

end Gauss

/-! ## Triangular exponents -/

/-- The triangular number `T(j) = j (j + 1) / 2`. -/
def tri (j : ℕ) : ℕ := j * (j + 1) / 2

lemma tri_succ (j : ℕ) : tri (j + 1) = tri j + (j + 1) := by
  unfold tri
  rw [show (j + 1) * (j + 1 + 1) = j * (j + 1) + (j + 1) * 2 by ring,
    Nat.add_mul_div_right _ _ (by norm_num)]

lemma le_tri (j : ℕ) : j ≤ tri j := by
  induction j with
  | zero => simp [tri]
  | succ j ih => rw [tri_succ]; omega

lemma tri_strictMono : StrictMono tri :=
  strictMono_nat_of_lt_succ fun j ↦ by rw [tri_succ]; omega

/-- `ex n m = T(m - n)` for the integer `m - n`, with `T(-j) = T(j - 1)`. -/
def ex (n m : ℕ) : ℕ := if n ≤ m then tri (m - n) else tri (n - m - 1)

lemma ex_add_left (n m : ℕ) : ex n m + n = m + ex (n + 1) m := by
  unfold ex
  by_cases h : n + 1 ≤ m
  · rw [ite_eq_left (by omega), ite_eq_left h, show m - n = (m - (n + 1)) + 1 by omega, tri_succ]
    omega
  · by_cases h' : n ≤ m
    · obtain rfl : m = n := by omega
      simp [add_comm]
    · rw [ite_eq_right h', ite_eq_right h, show n + 1 - m - 1 = (n - m - 1) + 1 by omega, tri_succ]
      omega

lemma ex_succ_succ (n k : ℕ) : ex (n + 1) (k + 1) = ex n k := by
  simp only [ex, Nat.add_le_add_iff_right, Nat.add_sub_add_right]

lemma ex_add_two (n k : ℕ) (hk : k ≤ 2 * n) :
    ex n k + n + 1 = (2 * n - k) + ex (n + 1) (k + 2) := by
  unfold ex
  by_cases h : n ≤ k
  · rw [ite_eq_left h, ite_eq_left (by omega), show k + 2 - (n + 1) = (k - n) + 1 by omega, tri_succ]
    omega
  · rw [ite_eq_right h]
    by_cases h' : n + 1 ≤ k + 2
    · obtain rfl : k = n - 1 := by omega
      rw [ite_eq_left h', show n - 1 + 2 - (n + 1) = 0 by omega, show n - (n - 1) - 1 = 0 by omega]
      omega
    · rw [ite_eq_right h', show n - k - 1 = (n + 1 - (k + 2) - 1) + 1 by omega, tri_succ]
      omega

lemma ex_two_mul (n : ℕ) : ex n (2 * n) = tri n := by
  rw [ex, ite_eq_left (by omega), show 2 * n - n = n by omega]

lemma ex_reflect (N j : ℕ) (hj : j < N) : ex N (N - 1 - j) = tri j := by
  simp [ex, show ¬ N ≤ N - 1 - j by omega, show N - (N - 1 - j) - 1 = j by omega]

lemma ex_add_self (N j : ℕ) : ex N (N + j) = tri j := by
  simp [ex]

/-! ## Finite Jacobi triple product -/

section Finite

open Polynomial

variable {A : Type*} [CommRing A]

/-- `∏_{i<n} (1 + x q^(i+1)) (x + q^i)`, a polynomial in `x` over `A`. -/
noncomputable def jtp (q : A) (n : ℕ) : A[X] :=
  ∏ i ∈ Finset.range n, ((1 + X * C (q ^ (i + 1))) * (X + C (q ^ i)))

lemma jtp_succ (q : A) (n : ℕ) :
    jtp q (n + 1) = jtp q n * (C (q ^ n) + C (1 + q ^ (2 * n + 1)) * X ^ 1 +
      C (q ^ (n + 1)) * X ^ 2) := by
  rw [jtp, Finset.prod_range_succ, ← jtp]
  congr 1
  simp only [map_add, map_one, map_pow]
  ring

/-- Finite Jacobi triple product: the coefficient of `x^m` in `jtp q n` is
`[2n, m] q^(T(m - n))`. -/
theorem coeff_jtp (q : A) : ∀ n m : ℕ, (jtp q n).coeff m = gauss q (2 * n) m * q ^ ex n m
  | 0, m => by
      rcases m with _ | m
      · simp [jtp, ex, tri]
      · simp [jtp, coeff_one]
  | n + 1, m => by
      have hsplit : ∀ (p : A[X]) (a b c : A), p * (C a + C b * X ^ 1 + C c * X ^ 2) =
          p * C a + p * C b * X ^ 1 + p * C c * X ^ 2 := by intros; ring
      rw [jtp_succ, hsplit, coeff_add, coeff_add, coeff_mul_X_pow', coeff_mul_X_pow',
        coeff_mul_C, coeff_mul_C, coeff_mul_C, show 2 * (n + 1) = 2 * n + 2 by ring]
      rcases m with _ | _ | k
      · simp only [coeff_jtp q n 0, gauss_zero_right, one_mul]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ← pow_add, ex_add_left, zero_add]
        ring
      · rw [ite_eq_left (by omega), ite_eq_right (by omega), coeff_jtp q n, coeff_jtp q n,
          gauss_two_step_one, Nat.sub_self, ← ex_succ_succ n 0]
        have e1 : q ^ ex n (0 + 1) * q ^ n = q ^ 1 * q ^ ex (n + 1) (0 + 1) := by
          rw [← pow_add, ← pow_add, ex_add_left]
        linear_combination gauss q (2 * n) (0 + 1) * e1
      · rw [ite_eq_left (by omega), ite_eq_left (by omega), show k + 1 + 1 - 1 = k + 1 by omega,
          show k + 1 + 1 - 2 = k by omega, coeff_jtp q n, coeff_jtp q n, coeff_jtp q n,
          gauss_two_step, ← ex_succ_succ n (k + 1)]
        have e1 : q ^ ex n (k + 1 + 1) * q ^ n = q ^ (k + 2) * q ^ ex (n + 1) (k + 1 + 1) := by
          rw [← pow_add, ← pow_add, ex_add_left]
        rcases Nat.lt_or_ge (2 * n) k with hk | hk
        · rw [gauss_eq_zero_of_lt q hk]
          linear_combination gauss q (2 * n) (k + 2) * e1
        · have e3 : q ^ ex n k * q ^ (n + 1) = q ^ (2 * n - k) * q ^ ex (n + 1) (k + 1 + 1) := by
            rw [← pow_add, ← pow_add, ← add_assoc, ex_add_two n k hk]
          linear_combination gauss q (2 * n) (k + 2) * e1 + gauss q (2 * n) k * e3


lemma natDegree_jtp_le (q : A) (n : ℕ) : (jtp q n).natDegree ≤ 2 * n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_jtp, gauss_eq_zero_of_lt q hN, zero_mul]

lemma jtp_succ_eq_mul (q : A) (n : ℕ) :
    jtp q (n + 1) = (X + 1) * ((∏ i ∈ Finset.range (n + 1), (1 + X * C (q ^ (i + 1)))) *
      ∏ i ∈ Finset.range n, (X + C (q ^ (i + 1)))) := by
  rw [jtp, Finset.prod_mul_distrib, Finset.prod_range_succ' (fun i ↦ X + C (q ^ i))]
  simp only [pow_zero, map_one]
  ring

/-- The derivative in `x` of the finite triple product at `x = -1`:
`(-1)^(n+1) (q;q)_(n+1) (q;q)_n = ∑_m m (-1)^m [2n+2, m] q^(T(m - n - 1))`. -/
theorem jtp_deriv (q : A) (n : ℕ) :
    (-1) ^ (n + 1) * qp q (n + 1) * qp q n =
      ∑ m ∈ Finset.range (2 * (n + 1) + 1),
        (m : A) * (-1) ^ m * gauss q (2 * (n + 1)) m * q ^ ex (n + 1) m := by
  have h1 : (derivative (jtp q (n + 1))).eval (-1) = (-1) ^ n * qp q (n + 1) * qp q n := by
    rw [jtp_succ_eq_mul, derivative_mul]
    simp only [derivative_add, derivative_X, derivative_one, add_zero, one_mul, eval_add,
      eval_mul, eval_X, eval_one, neg_add_cancel, zero_mul, eval_prod, eval_C]
    have ha : ∏ i ∈ Finset.range (n + 1), (1 + -1 * q ^ (i + 1)) = qp q (n + 1) :=
      Finset.prod_congr rfl fun i _ ↦ by ring
    have hb : ∏ i ∈ Finset.range n, (-1 + q ^ (i + 1)) = (-1) ^ n * qp q n := by
      have := Finset.prod_neg (s := Finset.range n) (fun i ↦ (1 : A) - q ^ (i + 1))
      rw [Finset.card_range] at this
      rw [qp, ← this]
      exact Finset.prod_congr rfl fun i _ ↦ by ring
    rw [ha, hb]
    ring
  have h2 : (derivative (jtp q (n + 1))).eval (-1) = ∑ m ∈ Finset.range (2 * (n + 1) + 1),
      (jtp q (n + 1)).coeff m * m * (-1) ^ (m - 1) := by
    rw [derivative_eval, sum_over_range' _ (fun _ ↦ by simp)]
    have := natDegree_jtp_le q (n + 1)
    omega
  calc (-1) ^ (n + 1) * qp q (n + 1) * qp q n = -((-1) ^ n * qp q (n + 1) * qp q n) := by ring
    _ = _ := by
      rw [← h1, h2, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [coeff_jtp]
      rcases m with _ | m
      · simp
      · rw [Nat.add_sub_cancel, pow_succ]
        ring
end Finite

/-! ## Pairing the terms `m` and `2N - 1 - m` -/

/-- `∑_{m ≤ 2N} m (-1)^m q^(T(m - N)) = (-1)^N ∑_{j < N} (-1)^j (2j+1) q^(T(j)) + 2N q^(T(N))`:
the terms `m = N - 1 - j` and `m = N + j` carry the same power `q^(T(j))`. -/
lemma sum_pairing {S : Type*} [CommRing S] (q : S) (N : ℕ) :
    ∑ m ∈ Finset.range (2 * N + 1), (m : S) * (-1) ^ m * q ^ ex N m =
      (-1) ^ N * ∑ j ∈ Finset.range N, (-1) ^ j * (2 * j + 1) * q ^ tri j +
        2 * N * q ^ tri N := by
  set g : ℕ → S := fun m ↦ (m : S) * (-1) ^ m * q ^ ex N m with hg
  have key : ∀ j ∈ Finset.range N,
      g (N - 1 - j) + g (N + j) = (-1) ^ N * ((-1) ^ j * (2 * j + 1) * q ^ tri j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨r, rfl⟩ : ∃ r, N = r + j + 1 := ⟨N - j - 1, by omega⟩
    simp only [hg]
    rw [ex_reflect _ _ hj, ex_add_self, show r + j + 1 - 1 - j = r by omega]
    have hs : (-1 : S) ^ j * (-1) ^ j = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    push_cast
    simp only [pow_add, pow_one]
    linear_combination (-(r : S) * (-1) ^ r * q ^ tri j) * hs
  calc ∑ m ∈ Finset.range (2 * N + 1), g m
      = ∑ m ∈ Finset.range (N + N), g m + g (2 * N) := by
        rw [Finset.sum_range_succ, two_mul]
    _ = ∑ j ∈ Finset.range N, (g (N - 1 - j) + g (N + j)) + g (2 * N) := by
        rw [Finset.sum_range_add, Finset.sum_add_distrib, Finset.sum_range_reflect]
    _ = _ := by
        rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
        simp only [hg, ex_two_mul, pow_mul]
        push_cast
        simp

/-! ## The limit -/

section Limit

open PowerSeries

variable (R : Type*) [CommRing R]

lemma dvd_prod_sub_one {a : R⟦X⟧} {t : Finset ℕ} {g : ℕ → R⟦X⟧} (h : ∀ i ∈ t, a ∣ g i - 1) :
    a ∣ ∏ i ∈ t, g i - 1 := by
  refine Finset.prod_induction g (fun y ↦ a ∣ y - 1) (fun x y hx hy ↦ ?_) (by simp) h
  have e : x * y - 1 = (x - 1) * y + (y - 1) := by ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_left hx y) hy

/-- The finite product `(q;q)_j` agrees with `pentagonalSeries R` modulo `X^(j+1)`. -/
lemma X_pow_dvd_pentagonalSeries_sub_qp (j : ℕ) :
    (X : R⟦X⟧) ^ (j + 1) ∣ pentagonalSeries R - qp X j := by
  rw [X_pow_dvd_iff]
  intro d hd
  obtain ⟨s, hs, hsj⟩ := ((coeff_prod_one_sub_X_pow_eventually_eq R d).and
    (Filter.eventually_ge_atTop (Finset.range j))).exists
  rw [map_sub, ← hs, sub_eq_zero, ← Finset.prod_sdiff hsj]
  have hP : (X : R⟦X⟧) ^ (j + 1) ∣ ∏ n ∈ s \ Finset.range j, (1 - X ^ (n + 1)) - 1 := by
    refine dvd_prod_sub_one R fun i hi ↦ ?_
    have hi' : j ≤ i := by simpa using (Finset.mem_sdiff.mp hi).2
    rw [sub_sub_cancel_left, dvd_neg]
    exact pow_dvd_pow X (by omega)
  obtain ⟨c, hc⟩ := hP
  have e : (∏ n ∈ s \ Finset.range j, (1 - X ^ (n + 1))) * ∏ n ∈ Finset.range j, (1 - X ^ (n + 1))
      = qp X j + X ^ (j + 1) * (c * qp X j) := by
    rw [← qp]
    linear_combination qp (X : R⟦X⟧) j * hc
  rw [e, map_add, coeff_X_pow_mul', ite_eq_right (by omega), add_zero]

lemma isUnit_pentagonalSeries : IsUnit (pentagonalSeries R) := by
  have h := X_pow_dvd_pentagonalSeries_sub_qp R 0
  rw [zero_add, pow_one, qp_zero, X_dvd_iff, map_sub, map_one, sub_eq_zero] at h
  rw [isUnit_iff_constantCoeff, h]
  exact isUnit_one

lemma mk_eq_mk_iff {k : ℕ} {a b : R⟦X⟧} :
    Ideal.Quotient.mk (Ideal.span {(X : R⟦X⟧) ^ k}) a =
      Ideal.Quotient.mk (Ideal.span {(X : R⟦X⟧) ^ k}) b ↔ X ^ k ∣ a - b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

lemma mk_qp {k j : ℕ} (h : k ≤ j + 1) :
    Ideal.Quotient.mk (Ideal.span {(X : R⟦X⟧) ^ k}) (qp X j) =
      Ideal.Quotient.mk (Ideal.span {(X : R⟦X⟧) ^ k}) (pentagonalSeries R) := by
  rw [mk_eq_mk_iff, ← dvd_neg, neg_sub]
  exact (pow_dvd_pow X h).trans (X_pow_dvd_pentagonalSeries_sub_qp R j)

/-- `[M, m] · f₁ ≡ 1` modulo `X^(a+1)` whenever `a ≤ m` and `a ≤ M - m`. -/
lemma X_pow_dvd_gauss_mul_sub_one {M m a : ℕ} (hm : m ≤ M) (ha1 : a ≤ m) (ha2 : a ≤ M - m) :
    (X : R⟦X⟧) ^ (a + 1) ∣ gauss X M m * pentagonalSeries R - 1 := by
  set π := Ideal.Quotient.mk (Ideal.span {(X : R⟦X⟧) ^ (a + 1)})
  have h := congrArg π (gauss_mul_qp X M m hm)
  rw [map_mul, map_mul, mk_qp R (by omega), mk_qp R (by omega), mk_qp R (by omega)] at h
  have hu : IsUnit (π (pentagonalSeries R)) := (isUnit_pentagonalSeries R).map π
  have h1 : π (gauss X M m) * π (pentagonalSeries R) = 1 :=
    hu.mul_right_cancel (by rw [h, one_mul])
  rw [← map_mul, ← map_one π] at h1
  exact (mk_eq_mk_iff R).mp h1

/-- Jacobi's identity modulo `X^N`:
`f₁^3 ≡ ∑_{j < N} (-1)^j (2j+1) X^(T(j))`. -/
theorem X_pow_dvd_pentagonalSeries_pow_three_sub (N : ℕ) :
    (X : R⟦X⟧) ^ N ∣ pentagonalSeries R ^ 3 -
      ∑ j ∈ Finset.range N, (-1 : R⟦X⟧) ^ j * (2 * (j : R⟦X⟧) + 1) * X ^ tri j := by
  rcases N with _ | n
  · simp
  set S := ∑ j ∈ Finset.range (n + 1), (-1 : R⟦X⟧) ^ j * (2 * (j : R⟦X⟧) + 1) * X ^ tri j with hS
  set T := ∑ m ∈ Finset.range (2 * (n + 1) + 1), (m : R⟦X⟧) * (-1) ^ m * X ^ ex (n + 1) m
    with hT
  have hA : X ^ (n + 1) ∣ (-1) ^ (n + 1) * pentagonalSeries R ^ 3 -
      (-1) ^ (n + 1) * qp X (n + 1) * qp X n * pentagonalSeries R := by
    rw [← mk_eq_mk_iff]
    simp only [map_mul, map_pow, mk_qp R (Nat.le_succ_of_le le_rfl), mk_qp R le_rfl]
    ring
  have hB : X ^ (n + 1) ∣ (∑ m ∈ Finset.range (2 * (n + 1) + 1),
      (m : R⟦X⟧) * (-1) ^ m * gauss X (2 * (n + 1)) m * X ^ ex (n + 1) m) *
        pentagonalSeries R - T := by
    rw [hT, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun m hm ↦ ?_
    rw [Finset.mem_range] at hm
    obtain ⟨a, ha1, ha2, hle⟩ : ∃ a, a ≤ m ∧ a ≤ 2 * (n + 1) - m ∧
        n + 1 ≤ ex (n + 1) m + (a + 1) := by
      by_cases h : n + 1 ≤ m
      · refine ⟨2 * (n + 1) - m, by omega, le_rfl, ?_⟩
        have := le_tri (m - (n + 1))
        rw [ex, ite_eq_left h]
        omega
      · refine ⟨m, le_rfl, by omega, ?_⟩
        have := le_tri (n + 1 - m - 1)
        rw [ex, ite_eq_right h]
        omega
    have hG := X_pow_dvd_gauss_mul_sub_one R (by omega) ha1 ha2
    have e : (m : R⟦X⟧) * (-1) ^ m * gauss X (2 * (n + 1)) m * X ^ ex (n + 1) m *
        pentagonalSeries R - (m : R⟦X⟧) * (-1) ^ m * X ^ ex (n + 1) m =
        (m : R⟦X⟧) * (-1) ^ m *
          (X ^ ex (n + 1) m * (gauss X (2 * (n + 1)) m * pentagonalSeries R - 1)) := by
      ring
    rw [e]
    refine Dvd.dvd.mul_left ((pow_dvd_pow X hle).trans ?_) _
    rw [pow_add]
    exact mul_dvd_mul_left _ hG
  have hC : X ^ (n + 1) ∣ T - (-1) ^ (n + 1) * S := by
    rw [hT, hS, sum_pairing, add_sub_cancel_left]
    exact dvd_mul_of_dvd_right (pow_dvd_pow X (le_tri (n + 1))) _
  have key : X ^ (n + 1) ∣ (-1) ^ (n + 1) * (pentagonalSeries R ^ 3 - S) := by
    have e : (-1) ^ (n + 1) * (pentagonalSeries R ^ 3 - S) =
        ((-1) ^ (n + 1) * pentagonalSeries R ^ 3 -
          (-1) ^ (n + 1) * qp X (n + 1) * qp X n * pentagonalSeries R) +
        ((∑ m ∈ Finset.range (2 * (n + 1) + 1),
          (m : R⟦X⟧) * (-1) ^ m * gauss X (2 * (n + 1)) m * X ^ ex (n + 1) m) *
            pentagonalSeries R - T) +
        (T - (-1) ^ (n + 1) * S) := by
      rw [← jtp_deriv]
      ring
    rw [e]
    exact dvd_add (dvd_add hA hB) hC
  have := key.mul_left ((-1) ^ (n + 1))
  rwa [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul] at this

/-- **Jacobi's identity** for the cube of Euler's product, coefficientwise:
`∏_{n ≥ 1} (1 - q^n)^3 = ∑_{k ≥ 0} (-1)^k (2k+1) q^(k(k+1)/2)`. -/
theorem pentagonalSeries_pow_three :
    pentagonalSeries R ^ 3 = PowerSeries.mk fun n ↦
      ∑ k ∈ Finset.range (n + 1), if tri k = n then (-1 : R) ^ k * (2 * k + 1) else 0 := by
  ext n
  have h := X_pow_dvd_pentagonalSeries_pow_three_sub R (n + 1)
  rw [X_pow_dvd_iff] at h
  have h' := h n (by omega)
  rw [map_sub, sub_eq_zero] at h'
  rw [h', coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have e : (-1 : R⟦X⟧) ^ k * (2 * (k : R⟦X⟧) + 1) = C ((-1 : R) ^ k * (2 * k + 1)) := by
    rw [map_mul, map_pow, map_neg, map_one, map_add, map_mul, map_natCast, map_one, map_ofNat]
  rw [e, coeff_C_mul_X_pow]
  simp only [eq_comm]

theorem coeff_pentagonalSeries_pow_three_tri (k : ℕ) :
    coeff (tri k) (pentagonalSeries R ^ 3) = (-1 : R) ^ k * (2 * k + 1) := by
  rw [pentagonalSeries_pow_three, coeff_mk, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    rw [ite_eq_right (tri_strictMono.injective.ne hj)]
  · intro hk
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_tri k))) hk

theorem coeff_pentagonalSeries_pow_three_of_ne {n : ℕ} (hn : ∀ k, tri k ≠ n) :
    coeff n (pentagonalSeries R ^ 3) = 0 := by
  rw [pentagonalSeries_pow_three, coeff_mk]
  exact Finset.sum_eq_zero fun k _ ↦ ite_eq_right (hn k)

end Limit

end Jacobi

open PowerSeries

/-- **Jacobi's identity** over any commutative ring:
`∏_{n ≥ 1} (1 - q^n)^3 = ∑_{k ≥ 0} (-1)^k (2k+1) q^(k(k+1)/2)`, stated coefficientwise. -/
theorem pentagonalSeries_pow_three_eq (R : Type*) [CommRing R] :
    pentagonalSeries R ^ 3 = PowerSeries.mk fun n ↦
      ∑ k ∈ Finset.range (n + 1), if k * (k + 1) / 2 = n then (-1 : R) ^ k * (2 * k + 1) else 0 :=
  Jacobi.pentagonalSeries_pow_three R

/-- The coefficient of `q^(k(k+1)/2)` in `∏_{n ≥ 1} (1 - q^n)^3` is `(-1)^k (2k+1)`. -/
theorem coeff_pentagonalSeries_pow_three (R : Type*) [CommRing R] (k : ℕ) :
    coeff (k * (k + 1) / 2) (pentagonalSeries R ^ 3) = (-1 : R) ^ k * (2 * k + 1) :=
  Jacobi.coeff_pentagonalSeries_pow_three_tri R k

open Classical in
/-- Jacobi's identity modulo 2: `∏ (1 - q^n)^3 ≡ ∑_{k ≥ 0} q^(k(k+1)/2) (mod 2)`. -/
theorem jacobi_mod_two :
    (PowerSeries.map (Int.castRingHom (ZMod 2)) (pentagonalSeries ℤ)) ^ 3 =
      PowerSeries.mk (fun n : ℕ ↦ if ∃ k : ℕ, k * (k + 1) / 2 = n then (1 : ZMod 2) else 0) := by
  ext n
  rw [← map_pow, coeff_map, coeff_mk]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [show k * (k + 1) / 2 = Jacobi.tri k from rfl, Jacobi.coeff_pentagonalSeries_pow_three_tri]
    simp [show (-1 : ZMod 2) = 1 from rfl, show (2 : ZMod 2) = 0 from rfl]
  · rw [Jacobi.coeff_pentagonalSeries_pow_three_of_ne ℤ fun k hk ↦ h ⟨k, hk⟩, map_zero]

end KeithZanello
