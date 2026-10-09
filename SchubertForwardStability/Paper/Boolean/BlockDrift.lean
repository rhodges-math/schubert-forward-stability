import SchubertForwardStability.Paper.Boolean.Drift
import SchubertForwardStability.Paper.Boolean.Centered

/-! # Mean drift and centered events over Boolean increment blocks

Positive drift sums over every block before the last supported position. A
nonpositive endpoint displacement then forces the corresponding centered sum
below the negative drift threshold.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory
open scoped BigOperators

/-- Every preterminal Boolean increment block has mean at least its length over twenty-seven. -/
theorem booleanMeanWalk_block_drift (n a k : ℕ) (hn : 3 ≤ n) (ha : a + k ≤ n - 1) :
    (1 / 27 : ℝ) * k ≤
      booleanMeanWalk n (a + k).succPNat - booleanMeanWalk n a.succPNat := by
  rw [← booleanMeanWalk_step_sum]
  calc
    _ = ∑ _t ∈ Finset.range k, (1 / 27 : ℝ) := by simp [mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' := Finset.mem_range.mp ht
      exact boolean_uniform_drift n hn (a + t).succPNat
        (by change a + t + 1 ≤ n - 1; omega)

/-- A backwards endpoint event forces a negative centered-block deviation of the fixed drift. -/
theorem boolean_backtrack_centered_le (n a k : ℕ) (hn : 3 ≤ n) (ha : a + k ≤ n - 1)
    (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+)
    (he : (recordWalk p.1 p.2 (a + k).succPNat : ℝ) ≤ recordWalk p.1 p.2 a.succPNat) :
    (∑ t ∈ Finset.range k, centeredBooleanStep n (a + t).succPNat p) ≤
      -((1 / 27 : ℝ) * k) := by
  rw [centeredBooleanStep_sum]
  have hMean := booleanMeanWalk_block_drift n a k hn ha
  linarith

end RecordStability
