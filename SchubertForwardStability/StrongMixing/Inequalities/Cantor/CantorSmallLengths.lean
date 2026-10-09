import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorParameters

/-!
# A uniform finite exception for the logarithmic Cantor construction

An elementary binary-power induction bounds the logarithm on natural lengths.
Consequently, failure of the retained-depth size condition occurs only below the
explicit constant 128, where the full short-interval quadratic estimate applies.
-/

namespace StrongMixing

private theorem pow_seven_linear (k : ℕ) : 16 * (k + 8) ≤ 2 ^ (7 + k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show 7 + (k + 1) = (7 + k) + 1 by omega, pow_succ]
    omega

/-- For every natural `n>=128`, `16*log(n)<=n*log(2)`. The proof uses bounds on the
natural logarithm of two and an induction over powers of two. -/
theorem log_nat_linear_le (n : ℕ) (hn : 128 ≤ n) :
    16 * Real.log n ≤ (n : ℝ) * Real.log 2 := by
  let b := Nat.log 2 n
  have hn0 : n ≠ 0 := by omega
  have hb : 7 ≤ b := (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) hn0).mpr
    (by norm_num; exact hn)
  have hlin : 16 * (b + 1) ≤ 2 ^ b := by
    have h := pow_seven_linear (b - 7)
    rw [show 7 + (b - 7) = b by omega, show b - 7 + 8 = b + 1 by omega] at h
    exact h
  have hpow : 2 ^ b ≤ n := Nat.pow_log_le_self 2 hn0
  have hR : 16 * ((b : ℝ) + 1) ≤ n := by exact_mod_cast hlin.trans hpow
  have hu : (n : ℝ) < (2 : ℝ) ^ (b + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  have hl := Real.log_lt_log (show 0 < (n : ℝ) by exact_mod_cast (show 0 < n by omega)) hu
  rw [Real.log_pow] at hl
  push_cast at hl
  have hm := mul_le_mul_of_nonneg_right hR (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  nlinarith only [hm, hl]

/-- If `n*delta<8` for `delta=log(2)/(2*log(n))`, then `n<128`.
This is an explicit finite exception bound, with no asymptotic hypothesis. -/
theorem cantor_small_length_lt (n : ℕ)
    (hsmall : (n : ℝ) * cantorDeletionFraction n < 8) : n < 128 := by
  by_contra hn'
  have hbig : 128 ≤ n := by omega
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  change (n : ℝ) * (Real.log 2 / (2 * Real.log n)) < 8 at hsmall
  rw [← mul_div_assoc] at hsmall
  have h := (div_lt_iff₀ (by positivity : 0 < 2 * Real.log n)).mp hsmall
  have hb := log_nat_linear_le n hbig
  nlinarith only [h, hb]

end StrongMixing
