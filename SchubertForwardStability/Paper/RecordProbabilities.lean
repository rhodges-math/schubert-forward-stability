import SchubertForwardStability.Permutations.Random.Records
import SchubertForwardStability.Permutations.Random.GrassRecordLaw
import SchubertForwardStability.Permutations.Random.BooleanRecords

/-! # Record probabilities for the three permutation families

For `1 <= j <= n`, a uniform permutation of `S_n` has a record at position `j` with
probability `1/j` (Rényi). For uniform Grassmannian and uniform Boolean permutations of
size `n`, the record probabilities are given by explicit binomial and Fibonacci formulas.

## Main results

* `RecordStability.record_probability_families`: the record probabilities of the three
  families.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Theorem 1.1.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory
open scoped BigOperators

/-- Uniform records have the four explicit symmetric, Grassmannian and Boolean probabilities. -/
theorem record_probability_families (n : ℕ) (j : ℕ+) (hj : (j : ℕ) ≤ n) :
    (unif (symmetricGroup n)).real {w | IsRecord w j} = ((j : ℕ) : ℝ)⁻¹ ∧
      (unif (grassmannian n)).real {w | IsRecord w j} =
        ((∑ k ∈ Finset.Icc (j : ℕ) n, (n.choose k : ℝ)) +
          (2 : ℝ) ^ ((j : ℕ) - 1) - n) / ((2 : ℝ) ^ n - n) ∧
      (unif (boolean n)).real {w | IsRecord w j} =
        ((Int.fib (2 * (n : ℤ) - 2) : ℝ) -
          (Int.fib (2 * (j : ℤ) - 4) : ℝ) *
            (Int.fib (2 * ((n : ℤ) - (j : ℤ)) - 1) : ℝ)) /
          (Int.fib (2 * (n : ℤ) - 1) : ℝ) ∧
      (unif (boolean n)).real {w | IsRecord w j} =
        (2 * Real.goldenRatio ^ (2 * (n : ℤ) - 2) +
          2 * Real.goldenRatio ^ (2 - 2 * (n : ℤ)) +
          Real.goldenRatio ^ (2 * (n : ℤ) - 4 * (j : ℤ) + 3) -
          Real.goldenRatio ^ (4 * (j : ℤ) - 2 * (n : ℤ) - 3)) /
        (Real.sqrt 5 * (Real.goldenRatio ^ (2 * (n : ℤ) - 1) +
          Real.goldenRatio ^ (1 - 2 * (n : ℤ)))) := by
  refine ⟨uniform_record_probability n j hj, grassmannian_record_probability n j hj,
    ?_, boolean_record_probability_golden n j hj⟩
  rw [boolean_record_probability_fib]
  congr 1
  exact_mod_cast (booleanRecordCount_fib n j hj)

end RecordStability
