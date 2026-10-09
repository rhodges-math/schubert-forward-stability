import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Tactic

/-! # Signed Fibonacci determinant identities

This file contains general results that extend Mathlib. Expanding Mathlib's addition formula
and Cassini's identity `Int.fib_succ_mul_fib_pred_sub_fib_sq` gives the Tagiuri--Vajda identity.
The shifted addition identity and its adjacent-product difference follow from the addition
formula.

## References

S. Vajda, Fibonacci & Lucas numbers, and the golden section, Ellis Horwood, 1989.
-/

namespace Int

/-- The Tagiuri--Vajda identity holds for arbitrary signed Fibonacci indices. -/
theorem fib_vajda (r a b : ℤ) :
    fib (r + a) * fib (r + b) - fib r * fib (r + a + b) =
      (-1 : ℤ) ^ r.natAbs * fib a * fib b := by
  have hA : fib (r + a) = fib (a - 1) * fib r + fib a * fib (r + 1) := by
    simpa only [add_comm a r] using fib_add a r
  have hB : fib (r + b) = fib (b - 1) * fib r + fib b * fib (r + 1) := by
    simpa only [add_comm b r] using fib_add b r
  have hAB : fib (r + a + b) =
      fib (a - 1) * fib (r + b) + fib a * fib (r + b + 1) := by
    have h := fib_add a (r + b)
    rw [show a + (r + b) = r + a + b by ring] at h
    exact h
  have hBNext : fib (r + b + 1) =
      fib (b - 1) * fib (r + 1) + fib b * fib (r + 2) := by
    have h := fib_add b (r + 1)
    rw [show b + (r + 1) = r + b + 1 by ring,
      show r + 1 + 1 = r + 2 by ring] at h
    exact h
  have hCass : fib (r + 1) ^ 2 - fib r * fib (r + 2) = (-1 : ℤ) ^ r.natAbs := by
    have h := fib_succ_mul_fib_pred_sub_fib_sq r
    have hPrev := fib_add_two (r - 1)
    rw [show r - 1 + 2 = r + 1 by ring, show r - 1 + 1 = r by ring] at hPrev
    have hPrev' : fib (r - 1) = fib (r + 1) - fib r := by linarith
    rw [hPrev'] at h
    rw [fib_add_two]
    calc
      _ = fib (r + 1) * (fib (r + 1) - fib r) - fib r ^ 2 := by ring
      _ = _ := h
  calc
    _ = fib a * fib b * (fib (r + 1) ^ 2 - fib r * fib (r + 2)) := by
      rw [hA, hAB, hBNext, hB]
      ring
    _ = _ := by rw [hCass]; ring

/-- The shifted Fibonacci addition identity. -/
theorem fib_add_one_mul (m k : ℤ) :
    fib (m + k + 1) = fib (m + 1) * fib (k + 1) + fib m * fib k := by
  have h := fib_add (m + 1) k
  rw [show m + 1 + k = m + k + 1 by ring, show m + 1 - 1 = m by ring] at h
  linarith

/-- Subtracting two shifted addition identities gives the adjacent-product difference. -/
theorem fib_adjacent_products (m k : ℤ) :
    fib (m + 1) * fib (k + 1) - fib (m - 1) * fib (k - 1) = fib (m + k) := by
  have hHigh := fib_add_one_mul m k
  have hLow := fib_add_one_mul (m - 1) (k - 1)
  rw [show m - 1 + (k - 1) + 1 = m + k - 1 by ring,
    show m - 1 + 1 = m by ring, show k - 1 + 1 = k by ring] at hLow
  have hRec := fib_add_two (m + k - 1)
  rw [show m + k - 1 + 2 = m + k + 1 by ring,
    show m + k - 1 + 1 = m + k by ring] at hRec
  linarith

end Int
