import SchubertForwardStability.Permutations.Classes.Intervals.IntervalEndpoints
import SchubertForwardStability.Permutations.Classes.Intervals.IntervalCounts

/-! # Support restrictions and final records in Boolean families

Intersecting an ambient Boolean family with a smaller support bound gives
exactly the smaller family. In size `r`, a record at position `r` means that `r` is
fixed, so the record fiber is the Boolean family of size `r-1`.
-/

namespace FinitaryPerm

open scoped Classical

/-- A Boolean family restricted to a smaller support bound is the smaller family. -/
theorem boolean_support_filter (n m : ℕ) (hm : m ≤ n) :
    (boolean n).filter (IsSupported m) = boolean m := by
  ext w
  simp only [Finset.mem_filter, mem_boolean]
  constructor
  · rintro ⟨⟨_, hBool⟩, hSmall⟩
    exact ⟨hSmall, hBool⟩
  · rintro ⟨hSmall, hBool⟩
    exact ⟨⟨hSmall.mono hm, hBool⟩, hSmall⟩

/-- At a positive support bound, the Boolean stabilization sublevel is the smaller family. -/
theorem filter_forwardStability_le_boolean (n m : ℕ) (hm : m ≤ n) (hPositive : 1 ≤ m) :
    (boolean n).filter (fun w => w.forwardStability ≤ m) = boolean m := by
  have h : (boolean n).filter (fun w => w.forwardStability ≤ m) =
      (boolean n).filter (IsSupported m) := by
    ext w
    simp only [Finset.mem_filter, forwardStability_le_iff w hPositive]
  rw [h, boolean_support_filter n m hm]

/-- In size `r`, the Boolean record fiber at position `r` is the Boolean family of size
`r-1`. -/
theorem booleanRecordFiber_last (r : ℕ+) :
    booleanRecordFiber (r : ℕ) r = boolean ((r : ℕ) - 1) := by
  ext w
  simp only [booleanRecordFiber, Finset.mem_filter, mem_boolean]
  constructor
  · rintro ⟨⟨hSupp, hBool⟩, hRec⟩
    exact ⟨(hSupp.fixed_last_iff r).mpr ((hSupp.isRecord_last_iff r).mp hRec), hBool⟩
  · rintro ⟨hSmall, hBool⟩
    have hSupp := hSmall.mono (Nat.sub_le (r : ℕ) 1)
    exact ⟨⟨hSupp, hBool⟩,
      (hSupp.isRecord_last_iff r).mpr ((hSupp.fixed_last_iff r).mp hSmall)⟩

/-- The final Boolean record count is the cardinality of the preceding ambient family. -/
theorem booleanRecordCount_last (r : ℕ+) :
    booleanRecordCount (r : ℕ) r = (boolean ((r : ℕ) - 1)).card := by
  rw [booleanRecordCount, booleanRecordFiber_last]

/-- The final Boolean record count has the preceding odd signed Fibonacci index. -/
theorem booleanRecordCount_last_fib (r : ℕ+) :
    (booleanRecordCount (r : ℕ) r : ℤ) = Int.fib (2 * (r : ℤ) - 3) := by
  rw [booleanRecordCount_last, card_boolean_int_fib_all]
  congr 1
  rw [Nat.cast_sub (by have hp := r.pos; omega : 1 ≤ (r : ℕ))]
  push_cast
  ring

end FinitaryPerm
