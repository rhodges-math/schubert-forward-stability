import SchubertForwardStability.SchubertPolynomials.Stability.Staircase
import SchubertForwardStability.SchubertPolynomials.Divided.Multiplication
import SchubertForwardStability.Permutations.Classes.CycleWord

/-! # Lowering a staircase by the initial cycle word

## Main results

The initial descending word lowers the next staircase to the current one.
The permutation operator of the successive-longest product has the same action.

## Implementation notes

The rightmost letter acts first. Thus the letters n, ..., 1 process the staircase
exponents from left to right. All commutative coefficient rings are allowed.
-/

namespace SchubertPolynomial

variable {R : Type*} [CommRing R]

/-- The first k successive adjacent operations lower the first k staircase exponents. -/
theorem initialWord_staircase_lowering (n k : ℕ) (hk : k ≤ n) :
    wordDividedDifference R (FinitaryPerm.initialDescendingWord k)
      (staircaseMonomial R (n + 1)) = MvPolynomial.monomial (loweredStaircase n k) 1 := by
  induction k with
  | zero =>
    rw [FinitaryPerm.initialDescendingWord_zero, wordDividedDifference_nil,
      LinearMap.id_apply, loweredStaircase_zero, staircaseMonomial]
  | succ k ih =>
    rw [FinitaryPerm.initialDescendingWord_succ, wordDividedDifference_cons,
      LinearMap.comp_apply, ih (by omega)]
    exact loweredStaircase_step n k (by omega)

/-- The descending cycle word lowers the next staircase monomial to the current one. -/
theorem wordDividedDifference_staircase (n : ℕ) :
    wordDividedDifference R (FinitaryPerm.initialDescendingWord n)
      (staircaseMonomial R (n + 1)) = staircaseMonomial R n := by
  rw [initialWord_staircase_lowering n n le_rfl, loweredStaircase_last]
  rfl

/-- The successive-longest permutation operator lowers the next staircase by one. -/
theorem permutationDividedDifference_staircase (n : ℕ) :
    permutationDividedDifference R
      (FinitaryPerm.longestElement n * FinitaryPerm.longestElement (n + 1))
      (staircaseMonomial R (n + 1)) = staircaseMonomial R n := by
  rw [permutationDividedDifference_eq _ (FinitaryPerm.isReduced_initialDescendingWord n)]
  exact wordDividedDifference_staircase n

end SchubertPolynomial
