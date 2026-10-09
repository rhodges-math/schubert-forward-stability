import SchubertForwardStability.Paper.Boolean.Means
import SchubertForwardStability.Permutations.ForMathlib.FibBounds

/-! # Exact expressions and a uniform positive Boolean drift gap

The pair-step expectation and record counts give both signed
Fibonacci expressions. Complementary-product and six-step growth estimates
give the fixed positive gap uniformly before the final ambient position.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Lemma 5.27 and (5.28).
-/

namespace RecordStability

open FinitaryPerm MeasureTheory

private theorem fib_family_pos (n : ℕ) :
    (0 : ℝ) < (Int.fib (2 * (n : ℤ) - 1) : ℝ) := by
  have h := Int.fib_two_mul_add_one_pos (n := (n : ℤ) - 1)
  rw [show 2 * ((n : ℤ) - 1) + 1 = 2 * (n : ℤ) - 1 by ring] at h
  exact_mod_cast h

private theorem fib_drift_reduce (n : ℤ) :
    2 * Int.fib (2 * n - 2) - Int.fib (2 * n - 1) = Int.fib (2 * n - 4) := by
  have h := Int.fib_add_two (2 * n - 3)
  rw [show 2 * n - 3 + 2 = 2 * n - 1 by ring,
    show 2 * n - 3 + 1 = 2 * n - 2 by ring] at h
  have hPrev := Int.fib_add_two (2 * n - 4)
  rw [show 2 * n - 4 + 2 = 2 * n - 2 by ring,
    show 2 * n - 4 + 1 = 2 * n - 3 by ring] at hPrev
  linarith

/-- Both signed Fibonacci expressions give the independent Boolean mean increment. -/
theorem boolean_drift_expression (n : ℕ) (i : ℕ+) (hi : (i : ℕ) ≤ n) :
    (∫ p, (recordWalkStep p.1 p.2 i : ℝ) ∂pairLaw (boolean n)) =
      ((2 * Int.fib (2 * (n : ℤ) - 2) - Int.fib (2 * (n : ℤ) - 1) -
        2 * Int.fib (2 * (i : ℤ) - 4) * Int.fib (2 * ((n : ℤ) - (i : ℤ)) - 1) : ℤ) : ℝ) /
      (Int.fib (2 * (n : ℤ) - 1) : ℝ) ∧
    (∫ p, (recordWalkStep p.1 p.2 i : ℝ) ∂pairLaw (boolean n)) =
      ((Int.fib (2 * (n : ℤ) - 4) -
        2 * Int.fib (2 * (i : ℤ) - 4) * Int.fib (2 * ((n : ℤ) - (i : ℤ)) - 1) : ℤ) : ℝ) /
      (Int.fib (2 * (n : ℤ) - 1) : ℝ) := by
  have hCount := congrArg (fun z : ℤ => (z : ℝ)) (booleanRecordCount_fib n i hi)
  push_cast at hCount
  have hD := (fib_family_pos n).ne'
  have hFirst :
      (∫ p, (recordWalkStep p.1 p.2 i : ℝ) ∂pairLaw (boolean n)) =
        ((2 * Int.fib (2 * (n : ℤ) - 2) - Int.fib (2 * (n : ℤ) - 1) -
          2 * Int.fib (2 * (i : ℤ) - 4) *
            Int.fib (2 * ((n : ℤ) - (i : ℤ)) - 1) : ℤ) : ℝ) /
        (Int.fib (2 * (n : ℤ) - 1) : ℝ) := by
    rw [integral_boolean_step, hCount]
    push_cast
    field_simp [hD]
    ring
  refine ⟨hFirst, ?_⟩
  rw [fib_drift_reduce] at hFirst
  exact hFirst

/-- The independent Boolean walk has mean increment at least one twenty-seventh before its end. -/
theorem boolean_uniform_drift (n : ℕ) (hn : 3 ≤ n) (i : ℕ+) (hi : (i : ℕ) ≤ n - 1) :
    (1 / 27 : ℝ) ≤ ∫ p, (recordWalkStep p.1 p.2 i : ℝ) ∂pairLaw (boolean n) := by
  obtain ⟨_, hExpr⟩ := boolean_drift_expression n i (hi.trans (Nat.sub_le _ _))
  rw [hExpr]
  have hi' : (i : ℤ) ≤ (n : ℤ) - 1 := by
    have h : (i : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by exact_mod_cast hi
    rw [Nat.cast_sub (by omega)] at h
    simpa only [Nat.cast_one] using h
  have hGap := Int.fib_complement_gap_le (n : ℤ) (i : ℤ) hi'
  apply (Int.fib_odd_gap_ratio n hn).trans
  apply (div_le_div_iff_of_pos_right (fib_family_pos n)).mpr
  exact_mod_cast hGap

end RecordStability
