import SchubertForwardStability.StrongMixing.Bernstein.PeelingScales
import SchubertForwardStability.StrongMixing.Bernstein.PeelingRemainder

/-!
# Explicit c-only constants for logarithmic peeling

The finite retained-piece and residual estimates are combined into positive
constants depending only on the geometric coefficient rate. The denominator
constant includes the log-log bound on the number of peeling stages.
-/

namespace StrongMixing

/-- A common per-row denominator rate dominates the retained rate and the
residual rate after multiplication by `log(n)`: `retainedRate+remainderRate/log(4)`. -/
noncomputable def peelingTotalRate (c : ℝ) : ℝ :=
  retainedRate c + remainderRate c / Real.log 4

/-- The total c-only denominator constant includes the log-log bound on the
number of retained pieces and the final residual. -/
noncomputable def peelingMprRate (c : ℝ) : ℝ :=
  peelingTotalRate c * (1 / Real.log 2 + 2 / Real.log (Real.log 4))

/-- The total c-only variance constant is the square of the sum of the retained
geometric scale coefficient and the final residual scale coefficient. -/
noncomputable def peelingMprVariance (c : ℝ) : ℝ :=
  (Real.sqrt (retainedVariance c) / (1 - Real.sqrt (1 / 2)) +
    Real.sqrt (remainderVariance c)) ^ 2

/-- The common per-row denominator rate is strictly positive for `c>0`. -/
theorem peelingTotalRate_pos {c : ℝ} (hc : 0 < c) : 0 < peelingTotalRate c := by
  have hr := retainedRate_pos hc
  have hs := remainderRate_pos hc
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  unfold peelingTotalRate
  positivity

/-- Both final c-only peeling constants are strictly positive for every positive
geometric coefficient rate. -/
theorem peelingMprConstants_pos {c : ℝ} (hc : 0 < c) :
    0 < peelingMprRate c ∧ 0 < peelingMprVariance c := by
  have hr := peelingTotalRate_pos hc
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : 0 < Real.log (Real.log 4) := Real.log_pos log_four_gt_one
  have hq := Real.sqrt_pos.mpr (retainedVariance_pos hc)
  have hs := Real.sqrt_pos.mpr (remainderVariance_pos hc)
  have hratio := peeling_ratio_bounds.2
  unfold peelingMprRate peelingMprVariance
  constructor <;> positivity

/-- For `n>=4`, the common per-row constant dominates the retained rate, and
its product with `log(n)` dominates the final residual rate. -/
theorem peelingRate_bounds {c : ℝ} (hc : 0 < c) (n : ℕ) (hn : 4 ≤ n) :
    retainedRate c ≤ peelingTotalRate c ∧
      remainderRate c ≤ peelingTotalRate c * Real.log n := by
  have hr := retainedRate_pos hc
  have hs := remainderRate_pos hc
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hln := (peeling_logs_pos n hn).1
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    (show (4 : ℝ) ≤ n by exact_mod_cast hn)
  have hm := mul_le_mul_of_nonneg_left hl
    (div_nonneg hs.le h4.le)
  have he : remainderRate c / Real.log 4 * Real.log 4 = remainderRate c := by field_simp
  unfold peelingTotalRate
  constructor
  · exact le_add_of_nonneg_right (div_nonneg hs.le h4.le)
  · nlinarith only [hm, he, mul_nonneg hr.le (by linarith : 0 ≤ Real.log n)]

end StrongMixing
