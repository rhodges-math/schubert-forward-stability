import SchubertForwardStability.SchubertPolynomials.Stability.Recurrence.SuffixDegrees
import SchubertForwardStability.SchubertPolynomials.Products.Degrees
import SchubertForwardStability.Permutations.Statistics.SuffixMaximum

/-! # Record maximum for Schubert product forward stability

## Main results

The positive support bound of the integral Schubert product equals the paired suffix
maximum and hence the paired global non-record maximum. This is the formula of Hardt and
Wallach: `FS(u,v) = max (Λ_i(u) + Λ_i(v) + i - 1)` over `i <= max(FS(u), FS(v)) + 1`, where
`Λ_i(w)` is the number of non-records of `w` at positions at least `i`.

* `SchubertPolynomial.productForwardStability_eq_recordBound`: the forward-stability formula.

## References

* A. Hardt and D. Wallach, *When do Schubert polynomial products stabilize?*,
  arXiv:2412.06976 (2024), Theorem 1.6.
-/

namespace SchubertPolynomial

open scoped Classical
open FinitaryPerm

/-- Product forward stability equals the positive paired suffix maximum. -/
theorem productForwardStability_eq_suffixBound (u v : FinitaryPerm ℕ+) :
    productForwardStability u v = pairSuffixBound u v := by
  apply le_antisymm
  · apply (productForwardStability_le_iff_degree u v (one_le_pairSuffixBound u v)).mpr
    intro i hi
    rw [schubert_degreeOf_eq_suffixCount, schubert_degreeOf_eq_suffixCount] at hi ⊢
    have hb : (i : ℕ) ≤ max u.forwardStability v.forwardStability := by
      by_contra hn
      have hi' := le_of_lt (lt_of_not_ge hn)
      have hu := suffixNonRecordCount_eq_zero u ((le_max_left _ _).trans hi')
      have hv := suffixNonRecordCount_eq_zero v ((le_max_right _ _).trans hi')
      rw [hu, hv] at hi
      exact (Nat.lt_irrefl 0) hi
    simpa only [Nat.add_assoc] using suffix_candidate_le hb hi
  · apply max_le (one_le_productForwardStability u v)
    apply Finset.sup_le
    intro i _
    by_cases hz : u.suffixNonRecordCount i + v.suffixNonRecordCount i = 0
    · rw [ite_eq_left hz]
      exact Nat.zero_le _
    · rw [ite_eq_right hz]
      have hi : 0 < (schubert ℤ u).degreeOf i + (schubert ℤ v).degreeOf i := by
        rw [schubert_degreeOf_eq_suffixCount, schubert_degreeOf_eq_suffixCount]
        exact Nat.pos_of_ne_zero hz
      have hb := (productForwardStability_le_iff_degree u v
        (one_le_productForwardStability u v)).mp le_rfl i hi
      rw [schubert_degreeOf_eq_suffixCount, schubert_degreeOf_eq_suffixCount] at hb
      simpa only [Nat.add_assoc] using hb

/-- The integral Schubert product support bound is the paired global record maximum
(Hardt and Wallach, Theorem 1.6). -/
theorem productForwardStability_eq_recordBound (u v : FinitaryPerm ℕ+) :
    productForwardStability u v = pairRecordBound u v := by
  rw [productForwardStability_eq_suffixBound, pairSuffixBound_eq_recordBound]

end SchubertPolynomial
