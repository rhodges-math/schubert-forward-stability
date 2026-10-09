import SchubertForwardStability.StrongMixing.Inequalities.RemovedCoordinates
import SchubertForwardStability.StrongMixing.Inequalities.Cantor.AdjustedCantorDepth

/-!
# A logarithmic quadratic bound on a full interval

A parameter-dependent deletion fraction is used only for this crude full-interval
remainder estimate. The explicit rounding penalty is quadratic, and the number of
levels is bounded by the real logarithm of the interval length.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A full interval of a centered measurable sequence bounded by `M>0`, with
geometric coefficient bound of rate `c>0`, has log-Laplace transform at
most `n*(t*M)^2*(6*K_c+384/c^2+2+3*log(n)/(c*log(2)))`. The explicit conditions
are `n>=1`, `t>0`, `t*M<=1/8`, and `t*M<=c/72`. No stationarity is required. -/
theorem interval_remainder_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c t : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (n : ℕ) (hn : 1 ≤ n) (a : ℤ) (ht : 0 < t) (hsmall : t * M ≤ 1 / 8)
    (hrate : t * M ≤ c / 72) :
    Real.log (∫ ω, Real.exp (t * ∑ i ∈ Finset.Ico a (a + n), X i ω) ∂μ) ≤
      n * (t * M) ^ 2 *
        (6 * (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) +
          384 / c ^ 2 + 2 + 3 * Real.log n / (c * Real.log 2)) := by
  let u := t * M
  let K := 1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))
  let C := 6 * K + 384 / c ^ 2
  have hu : 0 < u := mul_pos ht hM
  have hr : Real.exp (-2 * c) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : K ≤ C + 2 + 3 * Real.log n / (c * Real.log 2) := by
    have hp : 0 ≤ 384 / c ^ 2 + 3 * Real.log n / (c * Real.log 2) := by positivity
    dsimp [C]
    linarith
  change Real.log (∫ ω, Real.exp (t * ∑ i ∈ Finset.Ico a (a + n), X i ω) ∂μ) ≤
    n * u ^ 2 * (C + 2 + 3 * Real.log n / (c * Real.log 2))
  by_cases hnu : 1 ≤ (n : ℝ) * u
  · let δ := 3 * u / c
    let N := adjustedCantorDepth n u
    have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
    have hδ1 : δ ≤ 1 := by
      apply (div_le_iff₀ hc).mpr
      change u ≤ c / 72 at hrate
      linarith
    have hδmul : c * δ = 3 * u := by dsimp [δ]; field_simp
    have hsep : t * M ≤ c * δ / 3 := by
      change u ≤ c * δ / 3
      linarith only [hδmul]
    have hlen := adjustedCantorDepth_length_le δ n hu
    have hfinal : (t * M) ^ 2 * cantorLength δ n N ≤ c / 24 := by
      have hm := mul_le_mul_of_nonneg_left hlen hu.le
      change u ≤ c / 72 at hrate
      dsimp [N]
      nlinarith only [hm, hrate]
    have hp := adjustedCantorDepth_pow_le n hnu
    have hnuN : (n : ℝ) * u ≤ n := by
      have hs : u ≤ 1 := by change u ≤ 1 / 8 at hsmall; linarith
      simpa using mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
    have hquad := cantor_stopped_quadratic_le μ X hX hcenter hM hc hδ0 hδ1 hbound
      hmix n N a ht hsmall hfinal (hp.trans hnuN) hsep
    have hrem := cantor_complete_laplace_le μ X hX hM.le hδ0 hδ1 hbound ht.le n N a
    have hpen : u * ((N : ℝ) * δ * n + 2 * ((2 : ℝ) ^ N - 1)) ≤
        n * u ^ 2 * (3 * N / c + 2) := by
      have hp' : (2 : ℝ) ^ N - 1 ≤ (n : ℝ) * u := by dsimp [N]; linarith only [hp]
      have hm := mul_le_mul_of_nonneg_left hp' (by positivity : 0 ≤ 2 * u)
      calc
        _ = n * u ^ 2 * (3 * N / c) + 2 * u * ((2 : ℝ) ^ N - 1) := by
          dsimp [δ]
          ring
        _ ≤ n * u ^ 2 * (3 * N / c) + 2 * n * u ^ 2 := by nlinarith only [hm]
        _ = _ := by ring
    have hD := adjustedCantorDepth_log_le n hn
      (show u ≤ 1 by change u ≤ 1 / 8 at hsmall; linarith)
    have hDs : 3 * (N : ℝ) / c ≤ 3 * Real.log n / (c * Real.log 2) := by
      have hm := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 3 / c)
      dsimp [N]
      convert hm using 1 <;> field_simp
    calc
      _ ≤ n * u ^ 2 * C + u * ((N : ℝ) * δ * n + 2 * ((2 : ℝ) ^ N - 1)) :=
        hrem.trans (add_le_add hquad le_rfl)
      _ ≤ n * u ^ 2 * C + n * u ^ 2 * (3 * N / c + 2) := add_le_add le_rfl hpen
      _ = n * u ^ 2 * (C + 2 + 3 * N / c) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hDs) (by positivity)
  · have hs : |t| * n * M ≤ 1 := by
      rw [abs_of_pos ht]
      have h := (lt_of_not_ge hnu).le
      dsimp [u] at h
      nlinarith only [h]
    have h := geometric_interval_laplace_le μ X hX hcenter hM.le hc hbound hmix a n t hs
    calc
      _ ≤ t ^ 2 * n * M ^ 2 * K := h
      _ = n * u ^ 2 * K := by dsimp [u]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hC (by positivity)

end StrongMixing
