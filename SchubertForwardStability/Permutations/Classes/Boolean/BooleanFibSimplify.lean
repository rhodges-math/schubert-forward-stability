import SchubertForwardStability.Permutations.ForMathlib.FibIdentities
import SchubertForwardStability.Permutations.Classes.Boolean.BooleanFibProduct

/-! # Simplification of the Boolean record-count formula

Two shifted Fibonacci addition identities produce the intermediate difference.
Recurrence then turns the two boundary products into one product subtraction,
retaining arbitrary signed indices and the first-position convention.
-/

namespace FinitaryPerm

/-- The complementary adjacent Fibonacci products differ by the central even value. -/
theorem boolean_fib_intermediate (n j : ℤ) :
    Int.fib (2 * j - 1) * Int.fib (2 * n - 2 * j + 1) -
      Int.fib (2 * j - 3) * Int.fib (2 * n - 2 * j - 1) = Int.fib (2 * n - 2) := by
  have h := Int.fib_adjacent_products (2 * j - 2) (2 * n - 2 * j)
  rw [show 2 * j - 2 + 1 = 2 * j - 1 by ring,
    show 2 * j - 2 - 1 = 2 * j - 3 by ring,
    show 2 * j - 2 + (2 * n - 2 * j) = 2 * n - 2 by ring] at h
  exact h

/-- The two boundary products equal the simpler signed Fibonacci subtraction. -/
theorem boolean_fib_expressions (n j : ℤ) :
    Int.fib (2 * j - 3) * Int.fib (2 * n - 2 * j + 1) +
      (Int.fib (2 * j - 1) - Int.fib (2 * j - 3)) *
        (Int.fib (2 * n - 2 * j + 1) - Int.fib (2 * n - 2 * j - 1)) =
      Int.fib (2 * n - 2) - Int.fib (2 * j - 4) * Int.fib (2 * n - 2 * j - 1) := by
  have hInter := boolean_fib_intermediate n j
  have hRec := Int.fib_add_two (2 * j - 3)
  rw [show 2 * j - 3 + 2 = 2 * j - 1 by ring,
    show 2 * j - 3 + 1 = 2 * j - 2 by ring] at hRec
  have hPrev := Int.fib_add_two (2 * j - 4)
  rw [show 2 * j - 4 + 2 = 2 * j - 2 by ring,
    show 2 * j - 4 + 1 = 2 * j - 3 by ring] at hPrev
  have hExpand : Int.fib (2 * j - 1) =
      2 * Int.fib (2 * j - 3) + Int.fib (2 * j - 4) := by linarith
  rw [hExpand] at hInter ⊢
  nlinarith

/-- The Boolean record count is one central Fibonacci value minus a complementary product. -/
theorem booleanRecordCount_fib (n : ℕ) (j : ℕ+) (hj : (j : ℕ) ≤ n) :
    (booleanRecordCount n j : ℤ) = Int.fib (2 * (n : ℤ) - 2) -
      Int.fib (2 * (j : ℤ) - 4) * Int.fib (2 * ((n : ℤ) - (j : ℤ)) - 1) := by
  rw [booleanRecordCount_fib_product n j hj]
  have h := boolean_fib_expressions (n : ℤ) (j : ℤ)
  rw [show 2 * ((n : ℤ) - (j : ℤ)) - 1 = 2 * (n : ℤ) - 2 * (j : ℤ) - 1 by ring]
  exact h

end FinitaryPerm
