import SchubertForwardStability.StrongMixing.Inequalities.Cantor.AdjustedCantorDepth

/-!
# Fixed logarithmic parameters for a retained Cantor set

The deletion fraction is `log(2)/(2*log(n))`. Its retained depth is chosen from
the rounded size `n*delta/8`, independently of the Laplace parameter. Logarithmic
and integer-rounding bounds show that at least half of the coordinates are retained.
-/

namespace StrongMixing

/-- The fixed deletion fraction for a length `n` is `log(2)/(2*log(n))`.
This is a total real definition; quantitative estimates assume `n>=2`. -/
noncomputable def cantorDeletionFraction (n : ℕ) : ℝ := Real.log 2 / (2 * Real.log n)

/-- The fixed retained depth is the base-two natural logarithm of the natural
floor of `n*delta/8`, where `delta` is the fixed logarithmic deletion fraction. -/
noncomputable def cantorRetainedDepth (n : ℕ) : ℕ :=
  adjustedCantorDepth n (cantorDeletionFraction n / 8)

/-- For `n>=2`, the fixed deletion fraction is positive and at most one half. -/
theorem cantorDeletionFraction_bounds (n : ℕ) (hn : 2 ≤ n) :
    0 < cantorDeletionFraction n ∧ cantorDeletionFraction n ≤ 1 / 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ n by exact_mod_cast hn)
  have hln : 0 < Real.log n := hl2.trans_le hl
  unfold cantorDeletionFraction
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log n)).mpr
  nlinarith only [hl]

/-- If `n*delta>=8`, the fixed depth multiplicity is at most `n*delta/8`.
The deletion fraction and depth are both independent of the Laplace parameter. -/
theorem cantorRetainedDepth_pow_le (n : ℕ)
    (hlarge : 8 ≤ (n : ℝ) * cantorDeletionFraction n) :
    (2 : ℝ) ^ cantorRetainedDepth n ≤ n * cantorDeletionFraction n / 8 := by
  have h := adjustedCantorDepth_pow_le n (u := cantorDeletionFraction n / 8)
    (by nlinarith only [hlarge])
  simpa only [cantorRetainedDepth, mul_div_assoc] using h

/-- The terminal interval at the fixed retained depth satisfies `delta*length<=24`
for `n>=2`. This explicit bound includes depths equal to zero. -/
theorem cantorRetainedDepth_length_le (n : ℕ) (hn : 2 ≤ n) :
    cantorDeletionFraction n *
      cantorLength (cantorDeletionFraction n) n (cantorRetainedDepth n) ≤ 24 := by
  have hd := (cantorDeletionFraction_bounds n hn).1
  have h := adjustedCantorDepth_length_le (cantorDeletionFraction n) n
    (u := cantorDeletionFraction n / 8) (by positivity)
  change cantorDeletionFraction n / 8 *
    cantorLength (cantorDeletionFraction n) n (cantorRetainedDepth n) ≤ 3 at h
  nlinarith only [h]

/-- If `n>=2` and `n*delta>=8`, the fixed retained depth obeys
`depth*delta<=1/2-3*delta`. The margin comes from the multiplicity bound and the
logarithm of the factor eight. -/
theorem cantorRetainedDepth_fraction_le (n : ℕ) (hn : 2 ≤ n)
    (hlarge : 8 ≤ (n : ℝ) * cantorDeletionFraction n) :
    (cantorRetainedDepth n : ℝ) * cantorDeletionFraction n ≤
      1 / 2 - 3 * cantorDeletionFraction n := by
  let δ := cantorDeletionFraction n
  have hd : 0 < δ := (cantorDeletionFraction_bounds n hn).1
  have hd1 : δ ≤ 1 := ((cantorDeletionFraction_bounds n hn).2).trans (by norm_num)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow := cantorRetainedDepth_pow_le n hlarge
  have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ cantorRetainedDepth n) hpow
  rw [Real.log_pow, Real.log_div (mul_pos hn0 hd).ne' (by norm_num),
    Real.log_mul hn0.ne' hd.ne'] at hl
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [h8] at hl
  have hm := mul_le_mul_of_nonneg_right hl hd.le
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hd.le hd1
  have hbonus : δ * Real.log δ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd.le hlogδ
  have hid : δ * Real.log n = Real.log 2 / 2 := by
    dsimp [δ, cantorDeletionFraction]
    field_simp
  apply (mul_le_mul_iff_right₀ hl2).mp
  change Real.log 2 * ((cantorRetainedDepth n : ℝ) * δ) ≤ Real.log 2 * (1 / 2 - 3 * δ)
  nlinarith only [hm, hbonus, hid]

/-- For `n>=2` and `n*delta>=8`, the rounded Cantor block at the fixed
logarithmic depth retains at least half of the original coordinates. The statement
is independent of translation and of the Laplace parameter. -/
theorem cantorRetained_half (n : ℕ) (hn : 2 ≤ n) (a : ℤ)
    (hlarge : 8 ≤ (n : ℝ) * cantorDeletionFraction n) :
    (n : ℝ) / 2 ≤ (cantorBlock (cantorLength (cantorDeletionFraction n) n)
      0 a (cantorRetainedDepth n)).card := by
  have hd := cantorDeletionFraction_bounds n hn
  have hr := cantorLength_retained hd.1.le (hd.2.trans (by norm_num)) n (cantorRetainedDepth n)
  have hp := cantorRetainedDepth_pow_le n hlarge
  have hf := cantorRetainedDepth_fraction_le n hn hlarge
  have hm := mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
  rw [cantorBlock_card _ (cantorLength_fit _ _)]
  simp only [Nat.zero_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith only [hr, hp, hm, hlarge]

end StrongMixing
