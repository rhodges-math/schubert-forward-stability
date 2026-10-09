import SchubertForwardStability.SchubertPolynomials.Stability.Positive
import SchubertForwardStability.SchubertPolynomials.ForMathlib.PositiveDegrees
import SchubertForwardStability.Permutations.Statistics.SuffixRecurrence
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # Separate Schubert degrees and suffix non-records

## Main results

The degree of the integer Schubert polynomial `𝔖_w` in the variable `x_i` equals the
number of non-records of the sequence `w(i), w(i+1), ...`: the positions `j` such that
`w k > w j` for some `k` with `i <= k < j`. Combined with `Products/Degrees`, this gives the
forward-stability formula of Hardt and Wallach.

## References

* A. Hardt and D. Wallach, *When do Schubert polynomial products stabilize?*,
  arXiv:2412.06976 (2024), Theorem 1.6.
-/

namespace SchubertPolynomial

open scoped Classical
open FinitaryPerm

private theorem X_schubert_degree (w : FinitaryPerm ℕ+) (r i : ℕ+) :
    (MvPolynomial.X r * schubert ℤ w).degreeOf i =
      (schubert ℤ w).degreeOf i + (if i = r then 1 else 0) := by
  rw [MvPolynomial.degreeOf_mul_eq (MvPolynomial.X_ne_zero r) (schubert_ne_zero w),
    MvPolynomial.degreeOf_X, add_comm]

private theorem X_coeff_nonneg (r : ℕ+) (m : ℕ+ →₀ ℕ) :
    0 ≤ (MvPolynomial.X r : MvPolynomial ℕ+ ℤ).coeff m := by
  rw [MvPolynomial.coeff_X]
  split_ifs <;> omega

/-- Integer Schubert variable degrees satisfy the finite pivot maximum recurrence. -/
theorem schubert_degree_transition {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) (i : ℕ+) :
    (schubert ℤ w).degreeOf i =
      max ((schubert ℤ (w * swap r s)).degreeOf i + (if i = r then 1 else 0))
        ((transitionPositions (w * swap r s) r).sup fun q =>
          (schubert ℤ ((w * swap r s) * swap q r)).degreeOf i) := by
  have hp := MvPolynomial.coeff_mul_nonneg (X_coeff_nonneg r)
    (schubert_coeff_nonneg (w * swap r s))
  have hs := MvPolynomial.coeff_finsetSum_nonneg (transitionPositions (w * swap r s) r)
    (fun q => schubert ℤ ((w * swap r s) * swap q r))
    (fun q _ => schubert_coeff_nonneg ((w * swap r s) * swap q r))
  rw [schubert_transition h, transitionSum,
    MvPolynomial.degreeOf_add_eq_max_of_nonneg i hp hs, X_schubert_degree,
    MvPolynomial.degreeOf_sum_eq_sup_of_nonneg i _ _
      (fun q _ => schubert_coeff_nonneg ((w * swap r s) * swap q r))]

/-- A Schubert polynomial's separate variable degree is its suffix non-record count. -/
theorem schubert_degreeOf_eq_suffixCount (w : FinitaryPerm ℕ+) (i : ℕ+) :
    (schubert ℤ w).degreeOf i = w.suffixNonRecordCount i := by
  have hall : ∀ w : FinitaryPerm ℕ+, ∀ i : ℕ+,
      (schubert ℤ w).degreeOf i = w.suffixNonRecordCount i := by
    intro w
    refine pivotRankLt_wellFounded.induction
      (C := fun v => ∀ i : ℕ+, (schubert ℤ v).degreeOf i = v.suffixNonRecordCount i) w ?_
    intro v ih i
    by_cases hv : v = 1
    · subst v
      rw [schubert_one, MvPolynomial.degreeOf_one, suffixNonRecordCount_one]
    · obtain ⟨r, s, h⟩ := exists_increasingTailPivot hv
      calc
        (schubert ℤ v).degreeOf i =
            max ((schubert ℤ (v * swap r s)).degreeOf i + (if i = r then 1 else 0))
              ((transitionPositions (v * swap r s) r).sup fun q =>
                (schubert ℤ ((v * swap r s) * swap q r)).degreeOf i) :=
          schubert_degree_transition h i
        _ = max ((v * swap r s).suffixNonRecordCount i + (if i = r then 1 else 0))
              ((transitionPositions (v * swap r s) r).sup fun q =>
                ((v * swap r s) * swap q r).suffixNonRecordCount i) := by
          apply congrArg₂ max
          · exact congrArg (fun d => d + (if i = r then 1 else 0))
              (ih (v * swap r s) h.swapped_rank_lt i)
          · exact Finset.sup_congr rfl fun q hq =>
              ih ((v * swap r s) * swap q r) (h.transition_rank_lt hq) i
        _ = v.suffixNonRecordCount i := (h.suffix_count_transition i).symm
  exact hall w i

end SchubertPolynomial
