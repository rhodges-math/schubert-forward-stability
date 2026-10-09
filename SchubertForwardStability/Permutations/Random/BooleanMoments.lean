import SchubertForwardStability.Permutations.Random.BooleanRecords
import SchubertForwardStability.Permutations.Random.FamilyInstances

/-! # Means of uniform Boolean record indicators

The complementary indicator events turn record probabilities into
record and non-record means under the finite uniform measure.
-/

namespace FinitaryPerm

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- The mean Boolean non-record indicator is one minus the record probability. -/
theorem integral_boolean_nonRecord (n : ℕ) (j : ℕ+) :
    (∫ w, (w.nonRecordIndicator j : ℝ) ∂unif (boolean n)) =
      1 - (booleanRecordCount n j : ℝ) / (Int.fib (2 * (n : ℤ) - 1) : ℝ) := by
  have he : (fun w : FinitaryPerm ℕ+ => (w.nonRecordIndicator j : ℝ)) =
      {w : FinitaryPerm ℕ+ | IsRecord w j}ᶜ.indicator (fun _ => (1 : ℝ)) := by
    funext w
    by_cases hr : IsRecord w j <;> simp [nonRecordIndicator, hr]
  rw [he, integral_indicator_const (1 : ℝ) (by trivial), smul_eq_mul, mul_one,
    probReal_compl_eq_one_sub (by trivial), boolean_record_probability_fib]

/-- The mean Boolean record indicator is the record probability. -/
theorem integral_boolean_record (n : ℕ) (j : ℕ+) :
    (∫ w, ((1 - w.nonRecordIndicator j : ℕ) : ℝ) ∂unif (boolean n)) =
      (booleanRecordCount n j : ℝ) / (Int.fib (2 * (n : ℤ) - 1) : ℝ) := by
  have he : (fun w : FinitaryPerm ℕ+ => ((1 - w.nonRecordIndicator j : ℕ) : ℝ)) =
      {w : FinitaryPerm ℕ+ | IsRecord w j}.indicator (fun _ => (1 : ℝ)) := by
    funext w
    by_cases hr : IsRecord w j <;> simp [nonRecordIndicator, hr]
  rw [he, integral_indicator_const (1 : ℝ) (by trivial), smul_eq_mul, mul_one,
    boolean_record_probability_fib]

end FinitaryPerm
