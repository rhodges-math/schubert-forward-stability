import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# An explicit quadratic bound for an inverse exponential

The nonnegative exponential Taylor series controls the exponentially small
stopping error by a quadratic term with a constant depending only on its decay
parameter.
-/

namespace StrongMixing

/-- For positive real `a` and `u`, the inverse-scale exponential `exp(-a/u)` is
at most `2*u^2/a^2`. This follows from the quadratic term of the nonnegative
exponential series and has no smallness or asymptotic hypothesis. -/
theorem exp_inverse_sq_le {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    Real.exp (-a / u) ≤ 2 * u ^ 2 / a ^ 2 := by
  have h := Real.pow_div_factorial_le_exp (a / u) (div_nonneg ha.le hu.le) 2
  norm_num only [Nat.factorial, Nat.cast_ofNat] at h
  have hx : (a / u) ^ 2 / 2 * Real.exp (-(a / u)) ≤ 1 := by
    calc
      _ ≤ Real.exp (a / u) * Real.exp (-(a / u)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; simp
  have hs : (a / u) ^ 2 * Real.exp (-(a / u)) ≤ 2 := by linarith
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg u)
  have he : (a / u) ^ 2 * Real.exp (-(a / u)) * u ^ 2 =
      a ^ 2 * Real.exp (-(a / u)) := by
    field_simp
  rw [he] at hm
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  rw [neg_div]
  nlinarith only [hm]

end StrongMixing
