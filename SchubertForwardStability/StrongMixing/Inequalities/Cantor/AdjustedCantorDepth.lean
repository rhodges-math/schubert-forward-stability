import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorStopping

/-!
# Parameter-dependent depth for a full-interval remainder

For the crude full-interval estimate only, a depth based on `floor(n*u)` makes
the accumulated integer-rounding loss quadratic after multiplication by `u`.
The fixed retained sets used in the later peeling argument are unchanged.
-/

namespace StrongMixing

/-- The adjusted depth for the full-interval remainder is the base-two natural
logarithm of the natural floor of `n*u`. The definition is total for every real
`u`; quantitative estimates require `n*u >= 1`. -/
noncomputable def adjustedCantorDepth (n : ℕ) (u : ℝ) : ℕ := Nat.log 2 ⌊n * u⌋₊

/-- If `n*u >= 1`, the terminal multiplicity at the adjusted depth is at most
`n*u`. In particular, integer-rounding losses multiplied by `u` are quadratic. -/
theorem adjustedCantorDepth_pow_le (n : ℕ) {u : ℝ} (hnu : 1 ≤ n * u) :
    (2 : ℝ) ^ adjustedCantorDepth n u ≤ n * u := by
  have hq : 0 < ⌊(n : ℝ) * u⌋₊ := Nat.floor_pos.mpr hnu
  have h := Nat.pow_log_le_self 2 (Nat.ne_of_gt hq)
  have hR : (2 : ℝ) ^ adjustedCantorDepth n u ≤ (⌊(n : ℝ) * u⌋₊ : ℝ) := by
    exact_mod_cast h
  exact hR.trans (Nat.floor_le (by linarith : 0 ≤ (n : ℝ) * u))

/-- At the adjusted depth, the rounded terminal interval satisfies `u*length<=3`
for `u>0`. The estimate is uniform in the deletion fraction and original length. -/
theorem adjustedCantorDepth_length_le (δ : ℝ) (n : ℕ) {u : ℝ}
    (hu : 0 < u) :
    u * cantorLength δ n (adjustedCantorDepth n u) ≤ 3 := by
  have hp := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊(n : ℝ) * u⌋₊
  change ⌊(n : ℝ) * u⌋₊ < 2 ^ (adjustedCantorDepth n u + 1) at hp
  rw [pow_succ] at hp
  have hpR : (⌊(n : ℝ) * u⌋₊ : ℝ) < (2 : ℝ) ^ adjustedCantorDepth n u * 2 := by
    exact_mod_cast hp
  have hf := Nat.lt_floor_add_one ((n : ℝ) * u)
  have hpow1 : 1 ≤ (2 : ℝ) ^ adjustedCantorDepth n u :=
    one_le_pow₀ (by norm_num)
  have hcomp : (n : ℝ) * u ≤ 3 * (2 : ℝ) ^ adjustedCantorDepth n u := by linarith
  have hl : (2 : ℝ) ^ adjustedCantorDepth n u *
      cantorLength δ n (adjustedCantorDepth n u) ≤ n := by
    exact_mod_cast cantor_length_pow_le δ n (adjustedCantorDepth n u)
  have hm := mul_le_mul_of_nonneg_right hl hu.le
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < (2 : ℝ) ^ adjustedCantorDepth n u)).mp
  nlinarith only [hm, hcomp]

/-- For `u<=1`, the adjusted natural depth is at most the base-two natural
logarithm of `n`. Negative parameters are included because the natural floor
truncates them to zero. -/
theorem adjustedCantorDepth_le (n : ℕ) {u : ℝ} (hu : u ≤ 1) :
    adjustedCantorDepth n u ≤ Nat.log 2 n := by
  have hq : ⌊(n : ℝ) * u⌋₊ ≤ n := by
    have h : (n : ℝ) * u ≤ n := by
      simpa using mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
    exact Nat.floor_le_of_le (R := ℝ) h
  exact Nat.log_mono_right hq

/-- For `n>=1` and `u<=1`, the adjusted depth, as a real number, is at most
`log(n)/log(2)`. The bound holds for the rounded depth at every such `n`. -/
theorem adjustedCantorDepth_log_le (n : ℕ) (hn : 1 ≤ n) {u : ℝ} (hu : u ≤ 1) :
    (adjustedCantorDepth n u : ℝ) ≤ Real.log n / Real.log 2 := by
  have hp : (2 : ℝ) ^ Nat.log 2 n ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 n) hp
  rw [Real.log_pow] at hl
  have hD : (adjustedCantorDepth n u : ℝ) ≤ Nat.log 2 n := by
    exact_mod_cast adjustedCantorDepth_le n hu
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  exact (mul_le_mul_of_nonneg_right hD (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le).trans hl

end StrongMixing
