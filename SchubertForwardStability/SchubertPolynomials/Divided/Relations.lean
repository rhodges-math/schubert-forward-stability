import SchubertForwardStability.SchubertPolynomials.Divided.FiniteVariables

/-! # Nil-Coxeter relations on positive polynomial variables

## Main results

* `dividedDifference_braid`: consecutive adjacent operators satisfy the braid relation.
* `dividedDifference_commute`: separated adjacent operators commute.

## Implementation notes

Each polynomial is lifted to a finite initial variable interval containing both
operator supports. The finite arbitrary-ring identities then pass through renaming.
-/

namespace SchubertPolynomial

open Schubert.FinPermutation

variable {R : Type*} [CommRing R]

private theorem initial_position {n : ℕ} (i : ℕ+) (hi : (i : ℕ) < n) :
    (FinitaryPerm.positiveIndex n (AdjacentPosition.endingAt ⟨(i : ℕ), hi⟩ i.pos).left).val =
      i := by
  apply PNat.eq
  change (i : ℕ) - 1 + 1 = (i : ℕ)
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt i.pos)

/-- Consecutive positive-index divided differences satisfy the three-letter braid relation. -/
theorem dividedDifference_braid (i : ℕ+) (p : MvPolynomial ℕ+ R) :
    dividedDifference R i (dividedDifference R (i + 1) (dividedDifference R i p)) =
      dividedDifference R (i + 1) (dividedDifference R i (dividedDifference R (i + 1) p)) := by
  obtain ⟨n, hn, q, rfl⟩ := exists_initialRename p ((i : ℕ) + 2)
  have hi : (i : ℕ) < n := by omega
  have hj : ((i + 1 : ℕ+) : ℕ) < n := by change (i : ℕ) + 1 < n; omega
  let a := AdjacentPosition.endingAt ⟨(i : ℕ), hi⟩ i.pos
  let b := AdjacentPosition.endingAt ⟨((i + 1 : ℕ+) : ℕ), hj⟩ (i + 1).pos
  have ha : (FinitaryPerm.positiveIndex n a.left).val = i := initial_position i hi
  have hb : (FinitaryPerm.positiveIndex n b.left).val = i + 1 := initial_position (i + 1) hj
  have hab : a.right = b.left := by
    apply Fin.ext
    change (i : ℕ) - 1 + 1 = ((i + 1 : ℕ+) : ℕ) - 1
    change (i : ℕ) - 1 + 1 = (i : ℕ) + 1 - 1
    have := i.pos
    omega
  have h := congrArg (initialRename R n) (finiteDividedDifference_braid a b hab q)
  simpa only [← initialRename_dividedDifference, ha, hb] using h

/-- Positive-index divided differences at disjoint adjacent intervals commute. -/
theorem dividedDifference_commute (i j : ℕ+) (hgap : i + 1 < j ∨ j + 1 < i)
    (p : MvPolynomial ℕ+ R) :
    dividedDifference R i (dividedDifference R j p) =
      dividedDifference R j (dividedDifference R i p) := by
  obtain ⟨n, hn, q, rfl⟩ := exists_initialRename p (max (i : ℕ) (j : ℕ) + 1)
  have hi : (i : ℕ) < n := by omega
  have hj : (j : ℕ) < n := by omega
  let a := AdjacentPosition.endingAt ⟨(i : ℕ), hi⟩ i.pos
  let b := AdjacentPosition.endingAt ⟨(j : ℕ), hj⟩ j.pos
  have ha : (FinitaryPerm.positiveIndex n a.left).val = i := initial_position i hi
  have hb : (FinitaryPerm.positiveIndex n b.left).val = j := initial_position j hj
  have hseparated : Schubert.SeparatedAdjacentPositions a b := by
    rcases hgap with hgap | hgap
    · left
      change (i : ℕ) - 1 + 1 < (j : ℕ) - 1
      change (i : ℕ) + 1 < (j : ℕ) at hgap
      have := i.pos
      omega
    · right
      change (j : ℕ) - 1 + 1 < (i : ℕ) - 1
      change (j : ℕ) + 1 < (i : ℕ) at hgap
      have := j.pos
      omega
  have h := congrArg (initialRename R n) (finiteDividedDifference_commute a b hseparated q)
  simpa only [← initialRename_dividedDifference, ha, hb] using h

end SchubertPolynomial
