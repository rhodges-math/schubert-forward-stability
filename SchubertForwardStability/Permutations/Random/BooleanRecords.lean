import SchubertForwardStability.Permutations.Classes.Boolean.BooleanGolden
import SchubertForwardStability.Permutations.Random.FiniteEvents

/-! # Uniform Boolean record probabilities

The finite event mass and the Fibonacci family cardinality give record
probabilities directly. Signed Binet then yields the golden-ratio quotient.
-/

namespace FinitaryPerm

open MeasureTheory
open scoped Classical

/-- Uniform Boolean record probability is its exact count over the signed family count. -/
theorem boolean_record_probability_fib (n : ℕ) (j : ℕ+) :
    (unif (boolean n)).real {w | IsRecord w j} =
      (booleanRecordCount n j : ℝ) / (Int.fib (2 * (n : ℤ) - 1) : ℝ) := by
  rw [unif_real_event]
  change (booleanRecordCount n j : ℝ) / ((boolean n).card : ℝ) = _
  have h := congrArg (fun z : ℤ => (z : ℝ)) (card_boolean_int_fib_all n)
  simp only [Int.cast_natCast] at h
  rw [h]

private theorem sqrt_ratio (x y : ℝ) :
    (x / 5) / (y / Real.sqrt 5) = x / (Real.sqrt 5 * y) := by
  by_cases hy : y = 0
  · simp [hy]
  have hs : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  have hSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  field_simp [hs, hy]
  ring_nf
  rw [hSq]

/-- The uniform Boolean record probability is a quotient of golden-ratio expressions. -/
theorem boolean_record_probability_golden (n : ℕ) (j : ℕ+) (hj : (j : ℕ) ≤ n) :
    (unif (boolean n)).real {w | IsRecord w j} =
      (2 * Real.goldenRatio ^ (2 * (n : ℤ) - 2) +
        2 * Real.goldenRatio ^ (2 - 2 * (n : ℤ)) +
        Real.goldenRatio ^ (2 * (n : ℤ) - 4 * (j : ℤ) + 3) -
        Real.goldenRatio ^ (4 * (j : ℤ) - 2 * (n : ℤ) - 3)) /
      (Real.sqrt 5 * (Real.goldenRatio ^ (2 * (n : ℤ) - 1) +
        Real.goldenRatio ^ (1 - 2 * (n : ℤ)))) := by
  rw [boolean_record_probability_fib, booleanRecordCount_golden n j hj]
  have hOdd : Odd (2 * (n : ℤ) - 1) := ⟨(n : ℤ) - 1, by ring⟩
  rw [Real.signed_binet_odd _ hOdd]
  rw [show -(2 * (n : ℤ) - 1) = 1 - 2 * (n : ℤ) by ring]
  have hNumerator :
      (2 / 5 : ℝ) * Real.goldenRatio ^ (2 * (n : ℤ) - 2) +
        (2 / 5 : ℝ) * Real.goldenRatio ^ (2 - 2 * (n : ℤ)) +
        (1 / 5 : ℝ) * Real.goldenRatio ^ (2 * (n : ℤ) - 4 * (j : ℤ) + 3) -
        (1 / 5 : ℝ) * Real.goldenRatio ^ (4 * (j : ℤ) - 2 * (n : ℤ) - 3) =
      (2 * Real.goldenRatio ^ (2 * (n : ℤ) - 2) +
        2 * Real.goldenRatio ^ (2 - 2 * (n : ℤ)) +
        Real.goldenRatio ^ (2 * (n : ℤ) - 4 * (j : ℤ) + 3) -
        Real.goldenRatio ^ (4 * (j : ℤ) - 2 * (n : ℤ) - 3)) / 5 := by ring
  rw [hNumerator, sqrt_ratio]

end FinitaryPerm
