import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorStopping

/-!
# A closed Laplace estimate for a fixed retained Cantor set

The first interval below the terminal threshold controls all earlier mixing
errors. The resulting set is defined by its original length and deletion fraction,
not by the Laplace parameter.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

private theorem stop_exponent_le {c δ u : ℝ} (hc : 0 < c) (hu : 0 < u)
    (hsep : u ≤ c * δ / 3) :
    -c * δ * (c / (24 * u ^ 2)) ≤ -c / (8 * u) := by
  have hs : 3 * u ≤ c * δ := by linarith
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 8 * c * u)
  have hq : c / (8 * u) ≤ (c ^ 2 * δ) / (24 * u ^ 2) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 8 * u)
      (by positivity : 0 < 24 * u ^ 2)).mpr
    nlinarith only [hm]
  have he : (c ^ 2 * δ) / (24 * u ^ 2) = c * δ * (c / (24 * u ^ 2)) := by ring
  rw [he] at hq
  convert neg_le_neg hq using 1 <;> ring

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A prescribed-depth Cantor block has log-Laplace transform at most
`6*n*(t*M)^2*K_c + 3*n*exp(-c/(8*t*M))`. The proof stops at the first interval
of length at most `c/(24*(t*M)^2)`, without changing the prescribed retained set.
The conditions are `0<t*M<=1/8`, `t*M<=c*delta/3`, terminal interval smallness,
and `2^N<=n`, for a centered, bounded, geometrically mixing sequence. -/
theorem cantor_stopped_depth_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c δ t : ℝ}
    (hM : 0 < M) (hc : 0 < c) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (n N : ℕ) (a : ℤ) (ht : 0 < t) (hsmall : t * M ≤ 1 / 8)
    (hfinal : (t * M) ^ 2 * cantorLength δ n N ≤ c / 24)
    (hpow : (2 : ℝ) ^ N ≤ n) (hsep : t * M ≤ c * δ / 3) :
    Real.log (∫ ω, Real.exp
        (t * ∑ i ∈ cantorBlock (cantorLength δ n) 0 a N, X i ω) ∂μ) ≤
      6 * n * (t * M) ^ 2 *
        (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) +
          3 * n * Real.exp (-c / (8 * t * M)) := by
  let u := t * M
  have hu : 0 < u := mul_pos ht hM
  have hLast : (cantorLength δ n N : ℝ) ≤ c / (24 * u ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 24 * u ^ 2)).mpr
    nlinarith only [hfinal]
  obtain ⟨d, hd, hterminal, hprev⟩ :=
    exists_first_length_le (cantorLength δ n) N
      (c / (24 * u ^ 2)) hLast
  have hsize : u ^ 2 * (cantorLength δ n d : ℝ) ≤ c / 24 := by
    have h := (le_div_iff₀ (by positivity : 0 < 24 * u ^ 2)).mp hterminal
    nlinarith only [h]
  have htM : t * M ≤ c * δ := by
    have hcd := mul_nonneg hc.le hδ0
    linarith
  have hmain := cantor_fixed_terminal_le μ X hX hcenter hM hc hbound hmix
    (cantorLength δ n) (cantorLength_fit δ n) 0 a d (N - d)
      ht hsmall (by simpa only [Nat.zero_add] using hsize)
  have htotal : d + (N - d) = N := by omega
  simp only [Nat.zero_add, cantorLength, htotal] at hmain
  have herr := cantor_error_sum_le μ X hM.le hc.le hδ0 hδ1 hmix n d ht.le htM
    (fun k hk => (hprev k hk).le)
  have hexp : Real.exp (-c * δ * (c / (24 * u ^ 2))) ≤
      Real.exp (-c / (8 * t * M)) := by
    apply Real.exp_le_exp.mpr
    simpa only [u, mul_assoc] using stop_exponent_le hc hu hsep
  have hp0 : 0 ≤ (2 : ℝ) ^ d - 1 := by
    exact sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have herr' := herr.trans (mul_le_mul_of_nonneg_left hexp hp0)
  have hpD : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ N := by
    exact pow_le_pow_right₀ (by norm_num) hd
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hus : u ≤ 1 / 8 := hsmall
  have hmul := mul_le_mul_of_nonneg_left hus hn0
  have hcoef : 16 * n * u + ((2 : ℝ) ^ d - 1) ≤ 3 * n := by
    nlinarith only [hpow, hpD, hmul]
  refine (hmain.trans (add_le_add le_rfl herr')).trans ?_
  calc
    _ = 6 * n * u ^ 2 *
        (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) +
          (16 * n * u + ((2 : ℝ) ^ d - 1)) * Real.exp (-c / (8 * t * M)) := by
      dsimp [u]
      ring
    _ ≤ _ := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _))

/-- At the fixed depth `Nat.log 2 (n/8)`, the stopped Cantor log-Laplace bound
holds for `n >= 8`, `0<t*M<=1/8`, `(t*M)^2<=c/384`, and `t*M<=c*delta/3`.
The retained coordinate set is independent of the Laplace parameter. Its
half-retention follows separately from the depth-times-fraction condition. -/
theorem cantor_stopped_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c δ t : ℝ}
    (hM : 0 < M) (hc : 0 < c) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (n : ℕ) (hn : 8 ≤ n) (a : ℤ) (ht : 0 < t) (hsmall : t * M ≤ 1 / 8)
    (hsquare : (t * M) ^ 2 ≤ c / 384) (hsep : t * M ≤ c * δ / 3) :
    Real.log (∫ ω, Real.exp
        (t * ∑ i ∈ cantorBlock (cantorLength δ n) 0 a (fixedCantorDepth n), X i ω) ∂μ) ≤
      6 * n * (t * M) ^ 2 *
        (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) +
          3 * n * Real.exp (-c / (8 * t * M)) := by
  apply cantor_stopped_depth_le μ X hX hcenter hM hc hδ0 hδ1 hbound hmix n
    (fixedCantorDepth n) a ht hsmall _ _ hsep
  · have hl : (cantorLength δ n (fixedCantorDepth n) : ℝ) ≤ 16 := by
      exact_mod_cast fixedCantorLength_le δ n
    have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg (t * M))
    nlinarith
  · have h := (fixedCantorDepth_pow_le n hn).trans (Nat.div_le_self n 8)
    exact_mod_cast h

end StrongMixing
