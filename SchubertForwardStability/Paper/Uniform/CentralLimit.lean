import SchubertForwardStability.Paper.Uniform.Variance
import SchubertForwardStability.LimitTheorems.CentralLimit.Normalization

/-! # Variance-normalized uniform record central limit theorem

## Main results

Centered record sums satisfy the third-moment Lyapunov condition. Uniform record
counts, centered by their harmonic mean and divided by their standard deviation,
converge in distribution to the standard Gaussian.

## Implementation notes

The source measure is the uniform law on the symmetric group at each ambient size.
Initial zero-variance rows are covered by eventual-positive variance scaling.

## References

* A. Hardt, R. Hodges and H. Yin, *The record statistic and forward stability of Schubert
  products*, arXiv:2604.02964 (2026), Section 3.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory Filter
open scoped Classical BigOperators Topology

/-- The centered record row sums to the record count minus its harmonic mean. -/
theorem sum_centeredRecord (n : ℕ) (w : FinitaryPerm ℕ+) :
    (∑ i : Fin n, centeredRecord i.val.succPNat w) =
      (recordCount n w : ℝ) - (harmonic n : ℝ) := by
  have hc : (recordCount n w : ℝ) =
      ∑ i : Fin n, ((1 - w.nonRecordIndicator i.val.succPNat : ℕ) : ℝ) := by
    rw [recordCount_eq_sum, Nat.cast_sum, positions, Finset.sum_image]
    · rfl
    · intro a _ b _ hab
      exact (positiveIndex n).injective (Subtype.ext hab)
  simp only [centeredRecord, Finset.sum_sub_distrib, Nat.succPNat_coe, Nat.cast_succ]
  rw [← hc, sum_reciprocal_harmonic]

/-- The third absolute moment Lyapunov ratio of uniform records tends to zero. -/
theorem tendsto_record_third_scaled :
    Tendsto (fun n => (∑ i : Fin n, ∫ w, |centeredRecord i.val.succPNat w| ^ 3
      ∂unif (symmetricGroup n)) / Real.sqrt (recordVariance n) ^ 3) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => (1 : ℝ) / Real.sqrt (recordVariance n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_sqrt_recordVariance_atTop
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall fun n => div_nonneg
      (Finset.sum_nonneg fun i _ => integral_nonneg fun w => by positivity) (by positivity)
  · filter_upwards [tendsto_sqrt_recordVariance_atTop.eventually_gt_atTop 0] with n hn
    have he : (1 / Real.sqrt (recordVariance n)) * Real.sqrt (recordVariance n) ^ 3 =
        recordVariance n := by
      calc
        _ = Real.sqrt (recordVariance n) ^ 2 := by field_simp
        _ = _ := Real.sq_sqrt (recordVariance_nonneg n)
    apply (div_le_iff₀ (pow_pos hn 3)).mpr
    rw [he]
    exact sum_integral_abs_centeredRecord_cube_le n

/-- Uniform record counts, centered by their exact mean and variance, converge to Gaussian. -/
theorem uniform_centeredRecord_gaussian :
    TendstoInDistribution (fun (n : ℕ) (w : FinitaryPerm ℕ+) =>
      ((recordCount n w : ℝ) - (harmonic n : ℝ)) / Real.sqrt (recordVariance n))
      atTop id (fun n => unif (symmetricGroup n)) (gaussianReal 0 1) := by
  have h := LimitTheorems.tendstoInDistribution_sum_div
    (X := fun n (i : Fin n) => centeredRecord i.val.succPNat)
    (s := fun n => Real.sqrt (recordVariance n))
    (fun n i => memLp_centeredRecord n i.val.succPNat 3)
    (fun n i => integral_centeredRecord n i.val.succPNat
      (by change i.val + 1 ≤ n; omega))
    iIndepFun_centeredRecord
    (tendsto_sqrt_recordVariance_atTop.eventually_gt_atTop 0)
    (Filter.Eventually.of_forall fun n => by
      rw [sum_integral_centeredRecord_sq, Real.sq_sqrt (recordVariance_nonneg n)])
    tendsto_record_third_scaled
  have he : (fun (n : ℕ) (w : FinitaryPerm ℕ+) =>
      (∑ i : Fin n, centeredRecord i.val.succPNat w) / Real.sqrt (recordVariance n)) =
      (fun n w => ((recordCount n w : ℝ) - (harmonic n : ℝ)) /
        Real.sqrt (recordVariance n)) := by
    funext n w
    rw [sum_centeredRecord]
  rwa [he] at h

end RecordStability
