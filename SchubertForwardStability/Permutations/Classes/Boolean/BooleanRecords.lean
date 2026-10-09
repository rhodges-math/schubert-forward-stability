import SchubertForwardStability.Permutations.Classes.Tags.BlockTags
import SchubertForwardStability.Permutations.Statistics.Records
import Mathlib.Logic.Relation

/-! # Boolean record fibers and commutation moves

## Main definitions

The finite Boolean families fixing a position complement, the record fiber and
its two boundary cases, and the adjacent commuting move on reduced words.

## Implementation notes

Each family is a finite set of Boolean permutations of a fixed ambient size.
-/

namespace FinitaryPerm

open scoped Classical

/-- Boolean permutations fixing every position outside `I`. -/
noncomputable def booleanOn (n : ℕ) (I : Finset ℕ+) : Finset (FinitaryPerm ℕ+) :=
  (boolean n).filter fun w => ∀ i : ℕ+, i ∉ I → w i = i

/-- Boolean permutations with a record at position `j`. -/
noncomputable def booleanRecordFiber (n : ℕ) (j : ℕ+) : Finset (FinitaryPerm ℕ+) :=
  (boolean n).filter fun w => IsRecord w j

/-- The Boolean record count `N(n,j)`. -/
noncomputable def booleanRecordCount (n : ℕ) (j : ℕ+) : ℕ :=
  (booleanRecordFiber n j).card

/-- The record fiber with absent boundary generator immediately before `j`. -/
noncomputable def booleanBoundaryOne (n : ℕ) (j : ℕ+) : Finset (FinitaryPerm ℕ+) :=
  (booleanRecordFiber n j).filter fun w => blockTag n w ((j : ℕ) - 1) = .zero

/-- The complementary boundary case in the Boolean record fiber. -/
noncomputable def booleanBoundaryTwo (n : ℕ) (j : ℕ+) : Finset (FinitaryPerm ℕ+) :=
  booleanRecordFiber n j \ booleanBoundaryOne n j

/-- The finite interval of positive positions from `a` through `b`. -/
noncomputable def positionInterval (a b : ℕ) : Finset ℕ+ :=
  (positions b).filter fun i => a ≤ (i : ℕ)

/-- One adjacent commutation exchanges two letters whose indices differ by at least two. -/
def WordCommutation (a b : List ℕ+) : Prop :=
  ∃ pre suf : List ℕ+, ∃ i j : ℕ+,
    a = pre ++ i :: j :: suf ∧ b = pre ++ j :: i :: suf ∧
      (i + 1 < j ∨ j + 1 < i)

/-- A contiguous commuting inversion is an adjacent distant pair in decreasing order. -/
def HasCommutingInversion (word : List ℕ+) : Prop :=
  ∃ pre suf : List ℕ+, ∃ i j : ℕ+,
    word = pre ++ i :: j :: suf ∧ j + 1 < i

/-- A Boolean record fiber has exactly its Boolean and record membership conditions. -/
@[simp]
theorem mem_booleanRecordFiber (n : ℕ) (j : ℕ+) (w : FinitaryPerm ℕ+) :
    w ∈ booleanRecordFiber n j ↔ w ∈ boolean n ∧ IsRecord w j := by
  simp only [booleanRecordFiber, Finset.mem_filter]

/-- Every Boolean permutation has a record at the first position. -/
theorem booleanRecordFiber_first (n : ℕ) : booleanRecordFiber n 1 = boolean n := by
  ext w
  simp only [mem_booleanRecordFiber, isRecord_first, and_true]

end FinitaryPerm
