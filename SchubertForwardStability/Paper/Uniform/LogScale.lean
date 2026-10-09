import SchubertForwardStability.Paper.Uniform.CentralLimit
import SchubertForwardStability.LimitTheorems.Convergence.Deterministic
import SchubertForwardStability.LimitTheorems.Convergence.Slutsky

/-! # Logarithmically normalized uniform records

## Main results

Uniform record variance is asymptotic to log n. Harmonic and logarithmic centers
differ by a bounded amount, so Slutsky's theorem gives the logarithmically centered
and normalized record count's standard Gaussian limit.

## Implementation notes

The equality of the two normalization formulas includes the initial zero-denominator
rows. All source laws are the finite uniform permutation laws.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Section 3.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory Filter
open scoped Classical BigOperators Topology

/-- At positive sizes the harmonic and logarithmic centers differ by at most one. -/
theorem harmonic_sub_log_bounds (n : ℕ) (hn : 1 ≤ n) :
    (harmonic n : ℝ) - Real.log n ∈ Set.Icc (0 : ℝ) 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  have hlo : Real.log n ≤ (harmonic n : ℝ) := by
    calc
      _ ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hnpos (by linarith)
      _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic n
  exact ⟨sub_nonneg.mpr hlo, by linarith [harmonic_le_one_add_log n]⟩

/-- The uniform record variance is asymptotic to the logarithm of ambient size. -/
theorem tendsto_recordVariance_log :
    Tendsto (fun n : ℕ => recordVariance n / Real.log n) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htwo : Tendsto (fun n : ℕ => (2 : ℝ) / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hlo : Tendsto (fun n : ℕ => 1 - 2 / Real.log n) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub htwo
  have hhi : Tendsto (fun n : ℕ => 1 + 1 / Real.log n) atTop (𝓝 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hone
  have hb : ∀ᶠ n : ℕ in atTop, 1 - 2 / Real.log n ≤ recordVariance n / Real.log n ∧
      recordVariance n / Real.log n ≤ 1 + 1 / Real.log n := by
    filter_upwards [hlog.eventually_gt_atTop 0, eventually_ge_atTop 1] with n hln hn
    have hh := harmonic_sub_log_bounds n hn
    have hvl : Real.log n - 2 ≤ recordVariance n := by
      linarith [hh.1, harmonic_sub_two_le_recordVariance n]
    have hvh : recordVariance n ≤ Real.log n + 1 := by
      rw [recordVariance_eq_harmonic]
      linarith [hh.2, reciprocalSquares_nonneg n]
    constructor
    · apply (le_div_iff₀ hln).mpr
      have he : (1 - 2 / Real.log n) * Real.log n = Real.log n - 2 := by
        field_simp
      rwa [he]
    · apply (div_le_iff₀ hln).mpr
      have he : (1 + 1 / Real.log n) * Real.log n = Real.log n + 1 := by
        field_simp
      rwa [he]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)

/-- Exact and logarithmic record standard deviations have limiting ratio one. -/
theorem tendsto_recordScale_log :
    Tendsto (fun n : ℕ => Real.sqrt (recordVariance n) / Real.sqrt (Real.log n))
      atTop (𝓝 1) := by
  have h := (Real.continuous_sqrt.tendsto 1).comp tendsto_recordVariance_log
  simp only [Function.comp_def] at h
  have he : (fun n : ℕ => Real.sqrt (recordVariance n / Real.log n)) =
      (fun n => Real.sqrt (recordVariance n) / Real.sqrt (Real.log n)) := by
    funext n
    exact Real.sqrt_div (recordVariance_nonneg n) (Real.log n)
  rw [he] at h
  simpa only [Real.sqrt_one] using h

/-- The harmonic-to-logarithmic centering correction vanishes on the Gaussian scale. -/
theorem tendsto_recordMean_log :
    Tendsto (fun n : ℕ => ((harmonic n : ℝ) - Real.log n) / Real.sqrt (Real.log n))
      atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => Real.sqrt (Real.log n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / Real.sqrt (Real.log n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (harmonic_sub_log_bounds n hn).1 (Real.sqrt_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_le_div_of_nonneg_right (harmonic_sub_log_bounds n hn).2 (Real.sqrt_nonneg _)

/-- The logarithmically centered and normalized number of uniform records tends to Gaussian. -/
theorem uniform_record_gaussian :
    TendstoInDistribution (fun (n : ℕ) (w : FinitaryPerm ℕ+) =>
      ((recordCount n w : ℝ) - Real.log n) / Real.sqrt (Real.log n))
      atTop id (fun n => unif (symmetricGroup n)) (gaussianReal 0 1) := by
  have hmul := LimitTheorems.slutsky_mul uniform_centeredRecord_gaussian
    (LimitTheorems.tendstoInProbability_of_tendsto
      (μ := fun n => unif (symmetricGroup n)) tendsto_recordScale_log)
    (fun _ => measurable_const.aemeasurable)
  have hadd := LimitTheorems.slutsky_add hmul
    (LimitTheorems.tendstoInProbability_of_tendsto
      (μ := fun n => unif (symmetricGroup n)) tendsto_recordMean_log)
    (fun _ => measurable_const.aemeasurable)
  have he (n : ℕ) (w : FinitaryPerm ℕ+) :
      ((recordCount n w : ℝ) - (harmonic n : ℝ)) / Real.sqrt (recordVariance n) *
        (Real.sqrt (recordVariance n) / Real.sqrt (Real.log n)) +
        ((harmonic n : ℝ) - Real.log n) / Real.sqrt (Real.log n) =
      ((recordCount n w : ℝ) - Real.log n) / Real.sqrt (Real.log n) := by
    rcases lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · have hv := (Real.sqrt_pos.mpr (recordVariance_pos n hn)).ne'
      by_cases hl : Real.sqrt (Real.log n) = 0
      · simp only [hl, div_zero, mul_zero, add_zero]
      · field_simp
        ring
  have h := hadd.congr (T := id) (fun n => Filter.Eventually.of_forall (he n))
    (Filter.Eventually.of_forall (fun x : ℝ => by simp))
  exact h

end RecordStability
