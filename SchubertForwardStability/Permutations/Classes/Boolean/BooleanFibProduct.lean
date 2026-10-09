import SchubertForwardStability.Permutations.Classes.Intervals.BoundaryCounts
import SchubertForwardStability.Permutations.Classes.Intervals.IntervalCounts

/-! # The two-product Fibonacci record formula

The partition into the two boundary fibers and the factor-family bijections give the
record count. Signed Fibonacci numbers give the interval counts in both endpoint cases.
-/

namespace FinitaryPerm

open scoped Classical

private theorem initial_pred_card (n : ℕ) (r : ℕ+) (hr : (r : ℕ) ≤ n) :
    ((booleanOn n (positions ((r : ℕ) - 1))).card : ℤ) = Int.fib (2 * (r : ℤ) - 3) := by
  have h := card_booleanOn_initial_int n ((r : ℕ) - 1) ((Nat.sub_le _ _).trans hr)
  have hIdx : 2 * (((r : ℕ) - 1 : ℕ) : ℤ) - 1 = 2 * (r : ℤ) - 3 := by
    rw [Nat.cast_sub (by have hp := r.pos; omega : 1 ≤ (r : ℕ))]
    push_cast
    ring
  simpa only [hIdx] using h

private theorem interval_next_card (n : ℕ) (r : ℕ+) (hr : (r : ℕ) ≤ n) :
    ((booleanOn n (positionInterval ((r : ℕ) + 1) n)).card : ℤ) =
      Int.fib (2 * (n : ℤ) - 2 * (r : ℤ) - 1) := by
  have h := card_booleanOn_interval_int n (r + 1) (by
    change (r : ℕ) + 1 ≤ n + 1
    omega)
  have hIdx : 2 * (n : ℤ) - 2 * ((r + 1 : ℕ+) : ℤ) + 1 =
      2 * (n : ℤ) - 2 * (r : ℤ) - 1 := by
    change 2 * (n : ℤ) - 2 * (((r : ℕ) + 1 : ℕ) : ℤ) + 1 = _
    push_cast
    ring
  rw [hIdx] at h
  simpa only [PNat.add_coe, PNat.val_ofNat] using h

/-- The Boolean record count is the sum of its two signed Fibonacci factor products. -/
theorem booleanRecordCount_fib_product (n : ℕ) (r : ℕ+) (hr : (r : ℕ) ≤ n) :
    (booleanRecordCount n r : ℤ) =
      Int.fib (2 * (r : ℤ) - 3) * Int.fib (2 * (n : ℤ) - 2 * (r : ℤ) + 1) +
      (Int.fib (2 * (r : ℤ) - 1) - Int.fib (2 * (r : ℤ) - 3)) *
        (Int.fib (2 * (n : ℤ) - 2 * (r : ℤ) + 1) -
          Int.fib (2 * (n : ℤ) - 2 * (r : ℤ) - 1)) := by
  have hLsub : positions ((r : ℕ) - 1) ⊆ positions (r : ℕ) := by
    intro i hi
    rw [mem_positions] at hi ⊢
    exact hi.trans (Nat.sub_le _ _)
  have hRsub : positionInterval ((r : ℕ) + 1) n ⊆ positionInterval (r : ℕ) n := by
    intro i hi
    rw [mem_positionInterval] at hi ⊢
    exact ⟨hi.1, by omega⟩
  rw [booleanRecordCount_interval]
  push_cast
  rw [card_booleanOn_sdiff_cast n hLsub, card_booleanOn_sdiff_cast n hRsub,
    initial_pred_card n r hr, card_booleanOn_initial_int n r hr,
    card_booleanOn_interval_int n r (hr.trans (Nat.le_succ _)), interval_next_card n r hr]

end FinitaryPerm
