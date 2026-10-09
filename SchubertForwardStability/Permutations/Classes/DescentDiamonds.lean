import SchubertForwardStability.TypeA.Permutations.AdjacentLength
import SchubertForwardStability.TypeA.Polynomials.DividedDifferenceRelations

/-! # Descent diamonds for finite permutations

## Main definitions

* `HasDescentPair`: both specified adjacent positions are descents.
* `HasConsecutiveDescents`: the positions are consecutive and both are descents.

## Main results

Separated descents give a descending two-step diamond. Consecutive descents give
a descending three-step braid diamond. Every pair of adjacent positions is equal,
separated, or consecutive in one of the two orientations.

## Implementation notes

Finite positions and permutation multiplication use the type-A finite library.
-/

namespace FinitaryPerm

open Schubert (FinPermutation)
open Schubert.FinPermutation

variable {n : ℕ}

/-- Both specified finite adjacent positions are right descents. -/
def HasDescentPair (w : FinPermutation n) (a b : AdjacentPosition n) : Prop :=
  w.HasDescent a.left ∧ w.HasDescent b.left

/-- Two consecutive adjacent positions are both right descents. -/
def HasConsecutiveDescents (w : FinPermutation n) (a b : AdjacentPosition n) : Prop :=
  a.right = b.left ∧ HasDescentPair w a b

/-- Adjacent positions are equal, separated, or consecutive in either orientation. -/
theorem adjacentPosition_cases (a b : AdjacentPosition n) :
    a = b ∨ Schubert.SeparatedAdjacentPositions a b ∨
      a.right = b.left ∨ b.right = a.left := by
  by_cases heq : a.left = b.left
  · exact Or.inl (AdjacentPosition.ext heq)
  have hne : a.left.val ≠ b.left.val := fun h => heq (Fin.ext h)
  have hcases : a.left.val + 1 < b.left.val ∨ b.left.val + 1 < a.left.val ∨
      a.left.val + 1 = b.left.val ∨ b.left.val + 1 = a.left.val := by omega
  rcases hcases with h | h | h | h
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

/-- A separated adjacent swap preserves the other position's descent. -/
theorem descent_after_separated_swap (w : FinPermutation n) (a b : AdjacentPosition n)
    (hgap : Schubert.SeparatedAdjacentPositions a b) (hb : w.HasDescent b.left) :
    (w.rightAdjacentSwap a).HasDescent b.left := by
  obtain ⟨halbl, halbr, harbl, harbr⟩ := Schubert.separated_endpoint_ne a b hgap
  rw [hasDescent_left_iff] at hb ⊢
  rw [rightAdjacentSwap_apply_of_ne w a b.right halbr.symm harbr.symm,
    rightAdjacentSwap_apply_of_ne w a b.left halbl.symm harbl.symm]
  exact hb

/-- Two separated descents can be taken successively in either displayed order. -/
theorem descending_separated (w : FinPermutation n) (a b : AdjacentPosition n)
    (hgap : Schubert.SeparatedAdjacentPositions a b) (hdesc : HasDescentPair w a b) :
    IsDescendingWord w [a, b] ∧ IsDescendingWord w [b, a] := by
  exact ⟨⟨hdesc.1, descent_after_separated_swap w a b hgap hdesc.2, trivial⟩,
    ⟨hdesc.2, descent_after_separated_swap w b a (hgap.elim Or.inr Or.inl) hdesc.1,
      trivial⟩⟩

/-- The two separated two-step paths have the same permutation endpoint. -/
theorem separated_sorting_endpoint (w : FinPermutation n) (a b : AdjacentPosition n)
    (hgap : Schubert.SeparatedAdjacentPositions a b) :
    applyRightAdjacentWord [a, b] w = applyRightAdjacentWord [b, a] w := by
  apply Equiv.ext
  intro k
  change w (adjacentTransposition a (adjacentTransposition b k)) =
    w (adjacentTransposition b (adjacentTransposition a k))
  exact congrArg w (congrFun (Schubert.adjacentTransposition_commute_of_separated a b hgap) k)

private theorem consecutive_outer_ne (a b : AdjacentPosition n) (hab : a.right = b.left) :
    a.left ≠ b.right := (a.left_lt_right.trans (hab ▸ b.left_lt_right)).ne

/-- Swapping the left of two consecutive descents leaves a descent at the right position. -/
theorem descent_after_consecutive_left (w : FinPermutation n) (a b : AdjacentPosition n)
    (h : HasConsecutiveDescents w a b) : (w.rightAdjacentSwap a).HasDescent b.left := by
  have hxz := consecutive_outer_ne a b h.1
  have hz : b.right ≠ a.right := by rw [h.1]; exact b.left_ne_right.symm
  rw [hasDescent_left_iff,
    rightAdjacentSwap_apply_of_ne w a b.right hxz.symm hz, ← h.1,
    rightAdjacentSwap_apply_right]
  exact ((hasDescent_left_iff w b).mp h.2.2).trans
    (h.1 ▸ (hasDescent_left_iff w a).mp h.2.1)

/-- Swapping the right of two consecutive descents leaves a descent at the left position. -/
theorem descent_after_consecutive_right (w : FinPermutation n) (a b : AdjacentPosition n)
    (h : HasConsecutiveDescents w a b) : (w.rightAdjacentSwap b).HasDescent a.left := by
  have hxz := consecutive_outer_ne a b h.1
  have hxy : a.left ≠ b.left := by rw [← h.1]; exact a.left_ne_right
  rw [hasDescent_left_iff, h.1, rightAdjacentSwap_apply_left,
    rightAdjacentSwap_apply_of_ne w b a.left hxy hxz]
  exact ((hasDescent_left_iff w b).mp h.2.2).trans
    (h.1 ▸ (hasDescent_left_iff w a).mp h.2.1)

/-- The first two steps of the left braid path leave a descent at its left position. -/
theorem descent_after_left_braid_two (w : FinPermutation n) (a b : AdjacentPosition n)
    (hab : a.right = b.left) (hb : w.HasDescent b.left) :
    ((w.rightAdjacentSwap a).rightAdjacentSwap b).HasDescent a.left := by
  have hxz := consecutive_outer_ne a b hab
  have hxy : a.left ≠ b.left := by rw [← hab]; exact a.left_ne_right
  have hz : b.right ≠ a.right := by rw [hab]; exact b.left_ne_right.symm
  rw [hasDescent_left_iff, hab, rightAdjacentSwap_apply_left,
    rightAdjacentSwap_apply_of_ne w a b.right hxz.symm hz,
    rightAdjacentSwap_apply_of_ne (w.rightAdjacentSwap a) b a.left hxy hxz,
    rightAdjacentSwap_apply_left]
  simpa only [hab] using (hasDescent_left_iff w b).mp hb

/-- The first two steps of the right braid path leave a descent at its right position. -/
theorem descent_after_right_braid_two (w : FinPermutation n) (a b : AdjacentPosition n)
    (hab : a.right = b.left) (ha : w.HasDescent a.left) :
    ((w.rightAdjacentSwap b).rightAdjacentSwap a).HasDescent b.left := by
  have hxz := consecutive_outer_ne a b hab
  have hxy : a.left ≠ b.left := by rw [← hab]; exact a.left_ne_right
  have hz : b.right ≠ a.right := by rw [hab]; exact b.left_ne_right.symm
  rw [hasDescent_left_iff,
    rightAdjacentSwap_apply_of_ne (w.rightAdjacentSwap b) a b.right hxz.symm hz,
    rightAdjacentSwap_apply_right, ← hab, rightAdjacentSwap_apply_right,
    rightAdjacentSwap_apply_of_ne w b a.left hxy hxz]
  exact (hasDescent_left_iff w a).mp ha

/-- Two consecutive descents give descending three-step braid paths in both orders. -/
theorem descending_braid (w : FinPermutation n) (a b : AdjacentPosition n)
    (h : HasConsecutiveDescents w a b) :
    IsDescendingWord w [a, b, a] ∧ IsDescendingWord w [b, a, b] := by
  exact ⟨⟨h.2.1, descent_after_consecutive_left w a b h,
      descent_after_left_braid_two w a b h.1 h.2.2, trivial⟩,
    ⟨h.2.2, descent_after_consecutive_right w a b h,
      descent_after_right_braid_two w a b h.1 h.2.1, trivial⟩⟩

/-- The two consecutive three-step paths have the same permutation endpoint. -/
theorem braid_sorting_endpoint (w : FinPermutation n) (a b : AdjacentPosition n)
    (hab : a.right = b.left) :
    applyRightAdjacentWord [a, b, a] w = applyRightAdjacentWord [b, a, b] w := by
  apply Equiv.ext
  intro k
  change w (adjacentTransposition a (adjacentTransposition b (adjacentTransposition a k))) =
    w (adjacentTransposition b (adjacentTransposition a (adjacentTransposition b k)))
  exact congrArg w (congrFun (Schubert.adjacentTransposition_braid a b hab) k)

end FinitaryPerm
