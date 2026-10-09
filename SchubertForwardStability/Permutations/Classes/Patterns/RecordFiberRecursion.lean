import SchubertForwardStability.Permutations.Classes.Patterns.PatternRecordFibers
import SchubertForwardStability.Permutations.Classes.Patterns.PatternHighFibers

/-! # Deleting the final record in three-pattern avoidance fibers

For `π = 132` or `π = 231`, deleting the last record `r` of a record set factors the
record-fiber count of size `n` as the count of size `r-1` for the remaining records times
the number of `π`-avoiders of size `n-r`.

## Main results

* `PermutationPattern.recordFiber_recursion`: the recursion on the final record.
-/

namespace PermutationPattern

open FinitaryPerm
open scoped Classical

/-- Removing a maximal bounded position leaves positions strictly before it. -/
theorem erase_max_positions (R : Finset ℕ+) (r : ℕ+) (hLast : ∀ s ∈ R, s ≤ r) :
    R.erase r ⊆ positions ((r : ℕ) - 1) := by
  intro s hs
  obtain ⟨hne, hsR⟩ := Finset.mem_erase.mp hs
  have hLe := hLast s hsR
  have hValue : (s : ℕ) ≠ (r : ℕ) := fun h => hne (PNat.eq h)
  rw [mem_positions]
  change (s : ℕ) ≤ (r : ℕ) at hLe
  omega

/-- Deleting the last record factors either three-pattern avoidance fiber. -/
theorem recordFiber_recursion (n : ℕ) (π : PermutationPattern 3)
    (hπ : π = p132 ∨ π = p231) (R : Finset ℕ+) (hR : R ⊆ positions n)
    (r : ℕ+) (hr : r ∈ R) (hLast : ∀ s ∈ R, s ≤ r) :
    recordFiberCard n π R =
      recordFiberCard ((r : ℕ) - 1) π (R.erase r) * (avoiding (n - (r : ℕ)) π).card := by
  have hrBound := (mem_positions n r).mp (hR hr)
  have hrPos := r.pos
  have hSize : (r : ℕ) - 1 + (n - (r : ℕ)) + 1 = n := by omega
  have hIndex : ((r : ℕ) - 1).succPNat = r := by
    apply PNat.eq
    change (r : ℕ) - 1 + 1 = (r : ℕ)
    omega
  have hErase := erase_max_positions R r hLast
  rcases hπ with hπ | hπ <;> subst π
  · have h := card_recordFiber_joinHigh ((r : ℕ) - 1) (n - (r : ℕ)) (R.erase r) hErase
    rwa [hSize, hIndex, Finset.insert_erase hr] at h
  · have h := card_recordFiber_joinLow ((r : ℕ) - 1) (n - (r : ℕ)) (R.erase r) hErase
    rwa [hSize, hIndex, Finset.insert_erase hr] at h

end PermutationPattern
