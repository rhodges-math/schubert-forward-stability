import SchubertForwardStability.Permutations.Classes.Tags.TagRecovery
import SchubertForwardStability.Permutations.Classes.Tags.TagCounts
import Mathlib.Data.Int.Fib.Basic

/-! # Cardinalities of finite Boolean permutation families

The boundary-vector bijection transfers the number of valid boundary words to
the permutation family, including ambient size zero.
-/

namespace FinitaryPerm

/-- The finite Boolean family and its valid boundary vectors have equal cardinality. -/
theorem card_boolean_eq_tags (n : ℕ) : (boolean n).card = (tagWords (n - 1)).card :=
  Finset.card_nbij (booleanTags n) (booleanTags_bijOn n).1
    (booleanTags_bijOn n).2.1 (booleanTags_bijOn n).2.2

/-- Every finite Boolean family has the odd-index Fibonacci boundary-language count. -/
theorem card_boolean_nat_fib (n : ℕ) :
    (boolean n).card = Nat.fib (2 * (n - 1) + 1) := by
  rw [card_boolean_eq_tags, card_tagWords]

/-- Positive ambient sizes have the signed-index Fibonacci cardinality formula. -/
theorem card_boolean_int_fib (n : ℕ) (hn : 1 ≤ n) :
    ((boolean n).card : ℤ) = Int.fib (2 * (n : ℤ) - 1) := by
  have hIdx : ((2 * (n - 1) + 1 : ℕ) : ℤ) = 2 * (n : ℤ) - 1 := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hn]
    norm_num
    ring
  rw [card_boolean_nat_fib, ← hIdx, Int.fib_natCast]

end FinitaryPerm
