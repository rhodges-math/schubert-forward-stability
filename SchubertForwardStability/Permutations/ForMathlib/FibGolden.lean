import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/-! # Signed Binet formulas in golden-ratio coordinates

This file contains general results that extend Mathlib. The integer Binet formula is
expressed using the reciprocal negative golden ratio. Its even and odd specializations
retain arbitrary signed indices.
-/

namespace Real

/-- Binet's formula at every integer index in reciprocal golden-ratio coordinates. -/
theorem signed_binet (n : ℤ) : (Int.fib n : ℝ) =
    (goldenRatio ^ n - (-goldenRatio) ^ (-n)) / sqrt 5 := by
  rw [coe_intFib_eq]
  have hPower : (-goldenRatio) ^ (-n) = goldenConj ^ n := by
    rw [zpow_neg, ← inv_goldenConj, inv_zpow, inv_inv]
  rw [hPower]

/-- The even signed Binet formula has a difference of reciprocal powers. -/
theorem signed_binet_even (n : ℤ) (hn : Even n) : (Int.fib n : ℝ) =
    (goldenRatio ^ n - goldenRatio ^ (-n)) / sqrt 5 := by
  rcases hn with ⟨k, hk⟩
  have hNeg : Even (-n) := ⟨-k, by rw [hk]; ring⟩
  rw [signed_binet, hNeg.neg_zpow]

/-- The odd signed Binet formula has a sum of reciprocal powers. -/
theorem signed_binet_odd (n : ℤ) (hn : Odd n) : (Int.fib n : ℝ) =
    (goldenRatio ^ n + goldenRatio ^ (-n)) / sqrt 5 := by
  rw [signed_binet, hn.neg.neg_zpow, sub_neg_eq_add]

/-- The cube of the golden ratio is two plus the square root of five. -/
theorem goldenRatio_cube : goldenRatio ^ (3 : ℤ) = 2 + sqrt 5 := by
  rw [show (3 : ℤ) = (3 : ℕ) by rfl, zpow_natCast]
  calc
    _ = 2 * goldenRatio + 1 := by
      rw [pow_succ, goldenRatio_sq]
      nlinarith [goldenRatio_sq]
    _ = _ := by unfold goldenRatio; ring

/-- The reciprocal cube of the golden ratio is the square root of five minus two. -/
theorem goldenRatio_inv_cube : goldenRatio ^ (-3 : ℤ) = sqrt 5 - 2 := by
  have hInv : goldenRatio⁻¹ = goldenRatio - 1 := by
    rw [inv_goldenRatio, ← one_sub_goldenConj]
    ring
  rw [zpow_neg, show (3 : ℤ) = (3 : ℕ) by rfl, zpow_natCast, ← inv_pow, hInv]
  have hCube : goldenRatio ^ 3 = 2 + sqrt 5 := by
    simpa only [zpow_ofNat] using goldenRatio_cube
  have hSq := goldenRatio_sq
  nlinarith

end Real
