import SchubertForwardStability.Permutations.ForMathlib.FibGolden
import SchubertForwardStability.Permutations.Classes.Boolean.BooleanFibSimplify

/-! # Golden-ratio expressions for Boolean record counts

Signed Binet identities and the two reciprocal cube values expand the
Fibonacci subtraction formula into four golden-ratio powers.
-/

namespace FinitaryPerm

private theorem sqrt_five_inv : (Real.sqrt 5)⁻¹ = Real.sqrt 5 / 5 := by
  have hs : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  field_simp [hs]
  nlinarith

/-- The signed Fibonacci subtraction has a four-power golden-ratio expression. -/
theorem boolean_fib_golden (n j : ℤ) :
    (Int.fib (2 * n - 2) : ℝ) -
      (Int.fib (2 * j - 4) : ℝ) * (Int.fib (2 * n - 2 * j - 1) : ℝ) =
      (2 / 5 : ℝ) * Real.goldenRatio ^ (2 * n - 2) +
      (2 / 5 : ℝ) * Real.goldenRatio ^ (2 - 2 * n) +
      (1 / 5 : ℝ) * Real.goldenRatio ^ (2 * n - 4 * j + 3) -
      (1 / 5 : ℝ) * Real.goldenRatio ^ (4 * j - 2 * n - 3) := by
  let A := 2 * n - 2
  let B := 2 * j - 4
  let C := 2 * n - 2 * j - 1
  have hA : Even A := ⟨n - 1, by dsimp [A]; ring⟩
  have hB : Even B := ⟨j - 2, by dsimp [B]; ring⟩
  have hC : Odd C := ⟨n - j - 1, by dsimp [C]; ring⟩
  change (Int.fib A : ℝ) - (Int.fib B : ℝ) * (Int.fib C : ℝ) = _
  rw [Real.signed_binet_even A hA, Real.signed_binet_even B hB,
    Real.signed_binet_odd C hC, div_mul_div_comm,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  have hExpand :
      (Real.goldenRatio ^ A - Real.goldenRatio ^ (-A)) / Real.sqrt 5 -
        (Real.goldenRatio ^ B - Real.goldenRatio ^ (-B)) *
          (Real.goldenRatio ^ C + Real.goldenRatio ^ (-C)) / 5 =
      (Real.sqrt 5 * (Real.goldenRatio ^ A - Real.goldenRatio ^ (-A)) -
        (Real.goldenRatio ^ (B + C) + Real.goldenRatio ^ (B + (-C)) -
          Real.goldenRatio ^ ((-B) + C) - Real.goldenRatio ^ ((-B) + (-C)))) / 5 := by
    rw [zpow_add₀ Real.goldenRatio_ne_zero B C,
      zpow_add₀ Real.goldenRatio_ne_zero B (-C),
      zpow_add₀ Real.goldenRatio_ne_zero (-B) C,
      zpow_add₀ Real.goldenRatio_ne_zero (-B) (-C)]
    rw [div_eq_mul_inv (Real.goldenRatio ^ A - Real.goldenRatio ^ (-A)), sqrt_five_inv]
    ring
  rw [hExpand]
  have hBC : B + C = A + (-3) := by dsimp [A, B, C]; ring
  have hInvBC : (-B) + (-C) = (-A) + 3 := by dsimp [A, B, C]; ring
  have hDiff : B + (-C) = 4 * j - 2 * n - 3 := by dsimp [B, C]; ring
  have hInvDiff : (-B) + C = 2 * n - 4 * j + 3 := by dsimp [B, C]; ring
  rw [hBC, hInvBC, hDiff, hInvDiff, zpow_add₀ Real.goldenRatio_ne_zero A (-3),
    zpow_add₀ Real.goldenRatio_ne_zero (-A) 3,
    Real.goldenRatio_cube, Real.goldenRatio_inv_cube]
  have hInvA : -A = 2 - 2 * n := by dsimp [A]; ring
  rw [hInvA]
  dsimp only [A]
  ring

/-- The Boolean record count is a combination of four powers of the golden ratio. -/
theorem booleanRecordCount_golden (n : ℕ) (j : ℕ+) (hj : (j : ℕ) ≤ n) :
    (booleanRecordCount n j : ℝ) =
      (2 / 5 : ℝ) * Real.goldenRatio ^ (2 * (n : ℤ) - 2) +
      (2 / 5 : ℝ) * Real.goldenRatio ^ (2 - 2 * (n : ℤ)) +
      (1 / 5 : ℝ) * Real.goldenRatio ^ (2 * (n : ℤ) - 4 * (j : ℤ) + 3) -
      (1 / 5 : ℝ) * Real.goldenRatio ^ (4 * (j : ℤ) - 2 * (n : ℤ) - 3) := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (booleanRecordCount_fib n j hj)
  push_cast at h
  rw [show 2 * ((n : ℤ) - (j : ℤ)) - 1 = 2 * (n : ℤ) - 2 * (j : ℤ) - 1 by ring] at h
  exact h.trans (boolean_fib_golden n j)

end FinitaryPerm
