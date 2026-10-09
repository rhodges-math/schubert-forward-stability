import SchubertForwardStability.Permutations.ForMathlib.FibIdentities

/-! # Two-step growth bounds for Fibonacci numbers

This file contains general results that extend Mathlib. Monotonicity and the recurrence
bound each positive two-step growth factor between two and three. Iteration gives both
geometric bounds on every even stride.
-/

namespace Nat

/-- Fibonacci growth over two positions is at least a factor of two. -/
theorem fib_double_le_add_two (n : ℕ) : 2 * fib n ≤ fib (n + 2) := by
  rw [fib_add_two]
  have h := fib_le_fib_succ (n := n)
  omega

/-- Fibonacci growth over two positions is at most a factor of three at positive indices. -/
theorem fib_add_two_le_three (n : ℕ) (hn : 0 < n) : fib (n + 2) ≤ 3 * fib n := by
  have h := fib_mono (Nat.sub_le n 1)
  have hStep : fib (n + 1) = fib (n - 1) + fib n := fib_add_one hn.ne'
  rw [fib_add_two, hStep]
  omega

/-- Every even Fibonacci stride dominates the iterated factor-two lower bound. -/
theorem fib_pow_two_le_stride (n t : ℕ) : 2 ^ t * fib n ≤ fib (n + 2 * t) := by
  induction t with
  | zero => simp only [pow_zero, one_mul, mul_zero, add_zero, le_refl]
  | succ t ih =>
    have h := fib_double_le_add_two (n + 2 * t)
    rw [show n + 2 * (t + 1) = (n + 2 * t) + 2 by omega, pow_succ]
    nlinarith

/-- Every positive even Fibonacci stride satisfies the iterated factor-three upper bound. -/
theorem fib_stride_le_pow_three (n t : ℕ) (hn : 0 < n) :
    fib (n + 2 * t) ≤ 3 ^ t * fib n := by
  induction t with
  | zero => simp only [pow_zero, one_mul, mul_zero, add_zero, le_refl]
  | succ t ih =>
    have h := fib_add_two_le_three (n + 2 * t) (by omega)
    rw [show n + 2 * (t + 1) = (n + 2 * t) + 2 by omega, pow_succ]
    nlinarith

end Nat

namespace Int

/-- Positive odd Fibonacci indices obey the iterated factor-two lower growth bound. -/
theorem fib_odd_stride_le (n t : ℕ) (ht : t < n) :
    (2 : ℤ) ^ t * fib (2 * ((n : ℤ) - (t : ℤ)) - 1) ≤ fib (2 * (n : ℤ) - 1) := by
  have hGrowth := Nat.fib_pow_two_le_stride (2 * (n - t) - 1) t
  have hIdx : 2 * (n - t) - 1 + 2 * t = 2 * n - 1 := by omega
  rw [hIdx] at hGrowth
  have hSmall : fib (2 * ((n : ℤ) - (t : ℤ)) - 1) = Nat.fib (2 * (n - t) - 1) := by
    rw [show 2 * ((n : ℤ) - (t : ℤ)) - 1 = ((2 * (n - t) - 1 : ℕ) : ℤ) by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * (n - t)), Nat.cast_mul,
        Nat.cast_sub ht.le]
      push_cast
      ring, fib_natCast]
  have hLarge : fib (2 * (n : ℤ) - 1) = Nat.fib (2 * n - 1) := by
    rw [show 2 * (n : ℤ) - 1 = ((2 * n - 1 : ℕ) : ℤ) by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring, fib_natCast]
  rw [hSmall, hLarge]
  exact_mod_cast hGrowth

/-- Complementary Fibonacci products are bounded by their shifted even sum index. -/
theorem fib_complement_product_le (n j : ℤ) (hj : j ≤ n - 1) :
    fib (2 * j - 4) * fib (2 * (n - j) - 1) ≤ fib (2 * n - 6) := by
  have h := fib_add_one_mul (2 * j - 5) (2 * (n - j) - 2)
  rw [show 2 * j - 5 + (2 * (n - j) - 2) + 1 = 2 * n - 6 by ring,
    show 2 * j - 5 + 1 = 2 * j - 4 by ring,
    show 2 * (n - j) - 2 + 1 = 2 * (n - j) - 1 by ring] at h
  have hOdd : 0 ≤ fib (2 * j - 5) := by
    rw [show 2 * j - 5 = 2 * (j - 3) + 1 by ring]
    exact (fib_two_mul_add_one_pos (n := j - 3)).le
  have hEven : 0 ≤ fib (2 * (n - j) - 2) := by
    rw [fib_of_nonneg (by omega)]
    exact_mod_cast Nat.zero_le _
  have hProd := mul_nonneg hOdd hEven
  linarith

/-- Subtracting twice a complementary product leaves the preceding odd Fibonacci lower bound. -/
theorem fib_complement_gap_le (n j : ℤ) (hj : j ≤ n - 1) :
    fib (2 * n - 7) ≤ fib (2 * n - 4) - 2 * fib (2 * j - 4) *
      fib (2 * (n - j) - 1) := by
  have hProd := fib_complement_product_le n j hj
  have hRec := fib_add_two (2 * n - 6)
  rw [show 2 * n - 6 + 2 = 2 * n - 4 by ring,
    show 2 * n - 6 + 1 = 2 * n - 5 by ring] at hRec
  have hPrev := fib_add_two (2 * n - 7)
  rw [show 2 * n - 7 + 2 = 2 * n - 5 by ring,
    show 2 * n - 7 + 1 = 2 * n - 6 by ring] at hPrev
  linarith

/-- Six-step growth bounds give the uniform odd Fibonacci ratio gap from ambient size three. -/
theorem fib_odd_gap_ratio (n : ℕ) (hn : 3 ≤ n) :
    (1 / 27 : ℝ) ≤ (fib (2 * (n : ℤ) - 7) : ℝ) / (fib (2 * (n : ℤ) - 1) : ℝ) := by
  by_cases hThree : n = 3
  · subst n
    norm_num [fib, Nat.fib]
  have hn4 : 4 ≤ n := by omega
  have hPositive : 0 < 2 * n - 7 := by omega
  have hGrowth := Nat.fib_stride_le_pow_three (2 * n - 7) 3 hPositive
  have hIdx : 2 * n - 7 + 2 * 3 = 2 * n - 1 := by omega
  rw [hIdx] at hGrowth
  have hDen : (0 : ℝ) < (fib (2 * (n : ℤ) - 1) : ℝ) := by
    have h := fib_two_mul_add_one_pos (n := (n : ℤ) - 1)
    rw [show 2 * ((n : ℤ) - 1) + 1 = 2 * (n : ℤ) - 1 by ring] at h
    exact_mod_cast h
  apply (le_div_iff₀ hDen).mpr
  have hNum : fib (2 * (n : ℤ) - 7) = Nat.fib (2 * n - 7) := by
    rw [show 2 * (n : ℤ) - 7 = ((2 * n - 7 : ℕ) : ℤ) by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring, fib_natCast]
  have hDen' : fib (2 * (n : ℤ) - 1) = Nat.fib (2 * n - 1) := by
    rw [show 2 * (n : ℤ) - 1 = ((2 * n - 1 : ℕ) : ℤ) by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring, fib_natCast]
  rw [hNum, hDen']
  simp only [Int.cast_natCast]
  have hCast : (Nat.fib (2 * n - 1) : ℝ) ≤ 27 * Nat.fib (2 * n - 7) := by
    exact_mod_cast hGrowth
  linarith

end Int
