import SchubertForwardStability.Permutations.Classes.Intervals.ShiftedIntervals
import SchubertForwardStability.Permutations.Classes.Boolean.BooleanCounts
import SchubertForwardStability.Permutations.Classes.Intervals.BoundaryImages

/-! # Fibonacci cardinalities of Boolean interval families

Initial restrictions reduce to smaller ambient families. The translation
bijection gives final-interval cardinalities; the empty interval corresponds to the
signed Fibonacci value at negative one.
-/

namespace FinitaryPerm

open scoped Classical

/-- The signed odd-index Boolean cardinality also includes empty ambient size. -/
theorem card_boolean_int_fib_all (n : ℕ) :
    ((boolean n).card : ℤ) = Int.fib (2 * (n : ℤ) - 1) := by
  by_cases hZero : n = 0
  · subst n
    norm_num [card_boolean_nat_fib]
  · exact card_boolean_int_fib n (Nat.one_le_iff_ne_zero.mpr hZero)

/-- A contained initial Boolean interval has its signed Fibonacci cardinality. -/
theorem card_booleanOn_initial_int (n m : ℕ) (hm : m ≤ n) :
    ((booleanOn n (positions m)).card : ℤ) = Int.fib (2 * (m : ℤ) - 1) := by
  rw [booleanOn_positions n m hm, card_boolean_int_fib_all]

/-- A final Boolean interval, including an empty one, has its signed Fibonacci cardinality. -/
theorem card_booleanOn_interval_int (n : ℕ) (r : ℕ+) (hr : (r : ℕ) ≤ n + 1) :
    ((booleanOn n (positionInterval (r : ℕ) n)).card : ℤ) =
      Int.fib (2 * (n : ℤ) - 2 * (r : ℤ) + 1) := by
  have hp := r.pos
  have hm : (r : ℕ) - 1 ≤ n := by omega
  have hAmbient : (r : ℕ) - 1 + (n - ((r : ℕ) - 1)) = n := by omega
  have hLower : (r : ℕ) - 1 + 1 = (r : ℕ) := by omega
  have hCount := card_booleanOn_shifted ((r : ℕ) - 1) (n - ((r : ℕ) - 1))
  rw [hAmbient, hLower] at hCount
  rw [hCount, card_boolean_int_fib_all]
  congr 1
  rw [Nat.cast_sub hm, Nat.cast_sub (by omega : 1 ≤ (r : ℕ))]
  push_cast
  ring

/-- Subtracting a restricted Boolean subfamily subtracts its integer cardinality. -/
theorem card_booleanOn_sdiff_cast (n : ℕ) {I J : Finset ℕ+} (hIJ : I ⊆ J) :
    ((booleanOn n J \ booleanOn n I).card : ℤ) =
      ((booleanOn n J).card : ℤ) - ((booleanOn n I).card : ℤ) := by
  rw [Finset.card_sdiff_of_subset (booleanOn_mono n hIJ),
    Nat.cast_sub (Finset.card_le_card (booleanOn_mono n hIJ))]

end FinitaryPerm
