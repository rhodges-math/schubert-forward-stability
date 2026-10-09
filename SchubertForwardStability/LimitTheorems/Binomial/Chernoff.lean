import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

/-! # Symmetric-binomial Chernoff bound

The exponential generating function is a power of the hyperbolic cosine. Its
quadratic exponential bound yields the optimized upper-tail estimate.

## Main results

* `binomial_centered_exp`: the centered exponential generating function.
* `binomial_tail_exp`: the exponential-parameter upper-tail bound.
* `binomial_chernoff`: the optimized quadratic tail bound.
-/

open scoped BigOperators Classical

namespace LimitTheorems

/-- The centered symmetric-binomial exponential sum is a power of `cosh`. -/
theorem binomial_centered_exp (n : ℕ) (t : ℝ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) / 2 ^ n *
      Real.exp (t * ((k : ℝ) - n / 2))) = Real.cosh (t / 2) ^ n := by
  have he (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      Real.exp (t / 2) ^ k * Real.exp (-(t / 2)) ^ (n - k) =
        Real.exp (t * ((k : ℝ) - n / 2)) := by
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [←Real.exp_nat_mul, ←Real.exp_nat_mul, ←Real.exp_add,
      Nat.cast_sub hkn]
    congr 1
    ring
  rw [Real.cosh_eq, div_pow, add_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [he k hk]
  ring

/-- A nonnegative exponential parameter bounds the full symmetric-binomial upper tail. -/
theorem binomial_tail_exp (n : ℕ) (x t : ℝ) (ht : 0 ≤ t) :
    (∑ k ∈ Finset.range (n + 1),
      if (n : ℝ) / 2 + x ≤ k then (n.choose k : ℝ) / 2 ^ n else 0) ≤
      Real.exp (-t * x) * Real.cosh (t / 2) ^ n := by
  rw [←binomial_centered_exp, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : (n : ℝ) / 2 + x ≤ k
  · rw [ite_eq_left hk]
    have hp : 1 ≤ Real.exp (-t * x + t * ((k : ℝ) - n / 2)) := by
      apply Real.one_le_exp_iff.mpr
      have hd : 0 ≤ (k : ℝ) - n / 2 - x := by linarith
      nlinarith [mul_nonneg ht hd]
    have hm := mul_le_mul_of_nonneg_right hp
      (by positivity : 0 ≤ (n.choose k : ℝ) / 2 ^ n)
    rw [Real.exp_add] at hm
    nlinarith
  · rw [ite_eq_right hk]
    positivity

/-- The symmetric-binomial upper tail has the optimized quadratic Chernoff bound. -/
theorem binomial_chernoff (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 0 ≤ x) :
    (∑ k ∈ Finset.range (n + 1),
      if (n : ℝ) / 2 + x ≤ k then (n.choose k : ℝ) / 2 ^ n else 0) ≤
        Real.exp (-2 * x ^ 2 / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let t := 4 * x / n
  have ht : 0 ≤ t := by positivity
  have hc : Real.cosh (t / 2) ^ n ≤ Real.exp ((t / 2) ^ 2 / 2) ^ n :=
    pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) n
  have hb := (binomial_tail_exp n x t ht).trans
    (mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _))
  rw [←Real.exp_nat_mul, ←Real.exp_add] at hb
  have he : -t * x + (n : ℝ) * ((t / 2) ^ 2 / 2) = -2 * x ^ 2 / n := by
    dsimp [t]
    field_simp [hn0.ne']
    ring
  rwa [he] at hb

end LimitTheorems
