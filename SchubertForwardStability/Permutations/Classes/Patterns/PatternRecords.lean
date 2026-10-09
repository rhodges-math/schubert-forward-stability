import SchubertForwardStability.Permutations.Classes.PatternFamilies
import SchubertForwardStability.Permutations.Statistics.Records
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-! # Record fibers and deletion minors of permutation patterns

## Main definitions

Finite record fibers, their Catalan gap product, equality of bounded record fibers,
and standardization after deleting a specified pattern position.

## Implementation notes

Pattern positions use `Fin k`; record sets use positive positions.
The empty ambient group and empty record set are included in these objects.
-/

namespace PermutationPattern

open scoped Classical BigOperators

/-- The avoidance fiber with a specified record set in the ambient interval. -/
noncomputable def recordFiber {k : ℕ} (n : ℕ) (π : PermutationPattern k)
    (R : Finset ℕ+) : Finset (FinitaryPerm ℕ+) :=
  (avoiding n π).filter fun w => FinitaryPerm.recordSet n w = R

/-- The size of the avoidance fiber with record set `R`. -/
noncomputable def recordFiberCard {k : ℕ} (n : ℕ) (π : PermutationPattern k)
    (R : Finset ℕ+) : ℕ := (recordFiber n π R).card

/-- Fiber membership means pattern avoidance and exact equality of record sets. -/
@[simp]
theorem mem_recordFiber {k : ℕ} (n : ℕ) (π : PermutationPattern k)
    (R : Finset ℕ+) (w : FinitaryPerm ℕ+) :
    w ∈ recordFiber n π R ↔ w ∈ avoiding n π ∧ FinitaryPerm.recordSet n w = R := by
  simp only [recordFiber, Finset.mem_filter]

/-- The next record after `r`, with the external terminal position `n+1` appended. -/
noncomputable def nextRecord (n : ℕ) (R : Finset ℕ+) (r : ℕ+) : ℕ :=
  (insert (n + 1) ((R.image PNat.val).filter fun s => (r : ℕ) < s)).min'
    (Finset.insert_nonempty _ _)

/-- The product of Catalan numbers for the gaps between successive records. -/
noncomputable def recordGapProduct (n : ℕ) (R : Finset ℕ+) : ℕ :=
  ∏ r ∈ R, catalan (nextRecord n R r - (r : ℕ) - 1)

/-- The empty record set has empty Catalan gap product, equal to one. -/
@[simp]
theorem recordGapProduct_empty (n : ℕ) : recordGapProduct n ∅ = 1 := by
  simp only [recordGapProduct, Finset.prod_empty]

/-- Two same-rank patterns share record statistics when every bounded record fiber agrees. -/
def RecordEquivalent {k : ℕ} (π σ : PermutationPattern k) : Prop :=
  ∀ n, k ≤ n → ∀ R : Finset ℕ+, R ⊆ FinitaryPerm.positions n →
    recordFiberCard n π R = recordFiberCard n σ R

/-- The positive value of a finite pattern entry. -/
def positiveValue {k : ℕ} (π : PermutationPattern k) (i : Fin k) : ℕ+ :=
  ⟨(π i).val + 1, Nat.zero_lt_succ _⟩

/-- Pattern entries remain injective when written as positive values. -/
theorem positiveValue_injective {k : ℕ} (π : PermutationPattern k) :
    Function.Injective (positiveValue π) := by
  intro i j h
  apply π.injective
  apply Fin.ext
  have := congrArg PNat.val h
  change (π i).val + 1 = (π j).val + 1 at this
  exact Nat.add_right_cancel this

/-- The deletion minor is the standardization after omitting one pattern position. -/
noncomputable def deletionMinor {k : ℕ} (π : PermutationPattern (k + 1))
    (i : Fin (k + 1)) : PermutationPattern k :=
  standardize (fun j => positiveValue π (i.succAbove j))
    ((positiveValue_injective π).comp Fin.succAbove_right_injective)

/-- Deletion minors preserve the relative order of the undeleted entries. -/
theorem deletionMinor_lt_iff {k : ℕ} (π : PermutationPattern (k + 1))
    (i : Fin (k + 1)) (a b : Fin k) :
    deletionMinor π i a < deletionMinor π i b ↔ π (i.succAbove a) < π (i.succAbove b) := by
  rw [deletionMinor, standardize_lt_iff]
  change (π (i.succAbove a)).val + 1 < (π (i.succAbove b)).val + 1 ↔ _
  exact Nat.add_lt_add_iff_right

/-- The position of the maximum entry in a nonempty pattern. -/
def maximumPosition {k : ℕ} (π : PermutationPattern (k + 1)) : Fin (k + 1) :=
  π.symm (Fin.last k)

/-- The finite pattern record set, using positive-position indexing. -/
noncomputable def records {k : ℕ} (π : PermutationPattern k) : Finset ℕ+ :=
  FinitaryPerm.recordSet k (FinitaryPerm.ofFinite k π)

end PermutationPattern
