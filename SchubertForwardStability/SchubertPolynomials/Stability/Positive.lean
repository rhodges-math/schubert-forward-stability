import SchubertForwardStability.Permutations.Classes.PivotRank
import SchubertForwardStability.SchubertPolynomials.Stability.Recurrence.Transition

/-! # Nonnegative coefficients of integer Schubert polynomials

## Main results

Every coefficient is nonnegative. The proof uses the finite pivot transition and the
well-founded lexicographic descent rank.
-/

namespace SchubertPolynomial

open scoped Classical
open FinitaryPerm

/-- Every coefficient of an integer Schubert polynomial is nonnegative. -/
theorem schubert_coeff_nonneg (w : FinitaryPerm ℕ+) (m : ℕ+ →₀ ℕ) :
    0 ≤ (schubert ℤ w).coeff m := by
  have hall : ∀ w : FinitaryPerm ℕ+, ∀ m : ℕ+ →₀ ℕ,
      0 ≤ (schubert ℤ w).coeff m := by
    intro w
    refine pivotRankLt_wellFounded.induction
      (C := fun v => ∀ m : ℕ+ →₀ ℕ, 0 ≤ (schubert ℤ v).coeff m) w ?_
    intro v ih m
    by_cases hv : v = 1
    · subst v
      rw [schubert_one, MvPolynomial.coeff_one]
      split_ifs <;> omega
    · obtain ⟨r, s, h⟩ := exists_increasingTailPivot hv
      have hp := ih (v * swap r s) h.swapped_rank_lt
      have hs : 0 ≤ (transitionSum ℤ (v * swap r s) r).coeff m := by
        rw [transitionSum, MvPolynomial.coeff_sum]
        exact Finset.sum_nonneg fun q hq =>
          ih ((v * swap r s) * swap q r) (h.transition_rank_lt hq) m
      rw [schubert_transition h, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        MvPolynomial.coeff_X_mul']
      split_ifs
      · exact add_nonneg (hp _) hs
      · exact add_nonneg (le_refl 0) hs
  exact hall w m

end SchubertPolynomial
