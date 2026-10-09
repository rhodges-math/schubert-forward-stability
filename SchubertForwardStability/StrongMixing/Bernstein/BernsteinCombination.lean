import SchubertForwardStability.StrongMixing.Inequalities.Laplace.LaplaceCombination

/-! # Aggregation of Bernstein-shaped log-Laplace bounds

If finitely many random variables satisfy Bernstein-shaped bounds
`log E exp(u*Z_i) <= (sigma_i*u)^2/(1-kappa_i*u)`, then so does their sum, with
`sigma = sum sigma_i` and `kappa = sum kappa_i`. The variables may be dependent. This is the
aggregation lemma in the Bernstein inequality of Merlevède, Peligrad and Rio.

## References

* F. Merlevède, M. Peligrad and E. Rio, *Bernstein inequality and moderate deviations under
  strong mixing conditions*, High dimensional probability V: the Luminy volume, Inst. Math.
  Stat. (IMS) Collect. 5 (2009), 273-292, arXiv:1202.4777, the first lemma of the Appendix.
-/

open MeasureTheory
open scoped BigOperators

namespace StrongMixing

/-- Individual Bernstein-shaped log-Laplace bounds combine without independence:
the combined scale is the sum of the individual scales and the combined denominator
parameter is their sum. -/
theorem log_laplace_sum_bernstein_le {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (hs : s.Nonempty)
    (Z : ι → Ω → ℝ) (hZ : ∀ i ∈ s, AEMeasurable (Z i) μ) (σ κ : ι → ℝ)
    (hσ : ∀ i ∈ s, 0 < σ i) (hκ : ∀ i ∈ s, 0 ≤ κ i)
    (hRow : ∀ i ∈ s, ∀ u : ℝ, 0 ≤ u → κ i * u < 1 →
      Integrable (fun ω ↦ Real.exp (u * Z i ω)) μ ∧
        Real.log (∫ ω, Real.exp (u * Z i ω) ∂μ) ≤ (σ i * u) ^ 2 / (1 - κ i * u))
    (t : ℝ) (ht : 0 ≤ t) (hkt : (∑ i ∈ s, κ i) * t < 1) :
    Integrable (fun ω ↦ Real.exp (t * ∑ i ∈ s, Z i ω)) μ ∧
      Real.log (∫ ω, Real.exp (t * ∑ i ∈ s, Z i ω) ∂μ) ≤
        ((∑ i ∈ s, σ i) * t) ^ 2 / (1 - (∑ i ∈ s, κ i) * t) := by
  classical
  let S : ℝ := ∑ i ∈ s, σ i
  let K : ℝ := ∑ i ∈ s, κ i
  have hS : 0 < S := Finset.sum_pos hσ hs
  have hD : 0 < 1 - K * t := sub_pos.mpr hkt
  let w (i : ι) := σ i / S * (1 - K * t) + κ i * t
  have hw (i : ι) (hi : i ∈ s) : 0 < w i :=
    add_pos_of_pos_of_nonneg (mul_pos (div_pos (hσ i hi) hS) hD)
      (mul_nonneg (hκ i hi) ht)
  have hw1 : ∑ i ∈ s, w i = 1 := by
    dsimp [w]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_div]
    change S / S * (1 - K * t) + K * t = 1
    rw [div_self hS.ne']
    ring
  have hwi (i : ι) (hi : i ∈ s) : κ i * (t / w i) < 1 := by
    rw [← mul_div_assoc, div_lt_one (hw i hi)]
    have hp := mul_pos (div_pos (hσ i hi) hS) hD
    dsimp [w]
    linarith
  have hRi (i : ι) (hi : i ∈ s) :
      Integrable (fun ω ↦ Real.exp (t * Z i ω / w i)) μ ∧
        Real.log (∫ ω, Real.exp (t * Z i ω / w i) ∂μ) ≤
          (σ i * (t / w i)) ^ 2 / (1 - κ i * (t / w i)) := by
    simpa only [div_mul_eq_mul_div] using
      hRow i hi (t / w i) (div_nonneg ht (hw i hi).le) (hwi i hi)
  have hp := log_laplace_weighted_le μ s Z hZ w hw hw1 t (fun i hi ↦ (hRi i hi).1)
  refine ⟨hp.1, hp.2.trans ?_⟩
  have hterm (i : ι) (hi : i ∈ s) :
      w i * ((σ i * (t / w i)) ^ 2 / (1 - κ i * (t / w i))) =
        σ i * S * t ^ 2 / (1 - K * t) := by
    have hrel : w i - κ i * t = σ i / S * (1 - K * t) := by dsimp [w]; ring
    have he : 1 - κ i * (t / w i) = σ i / S * (1 - K * t) / w i := by
      field_simp [(hw i hi).ne', hS.ne'] at hrel ⊢
      nlinarith [hrel]
    rw [he]
    field_simp [(hw i hi).ne', hS.ne', (hσ i hi).ne', hD.ne']
  calc
    _ ≤ ∑ i ∈ s, w i *
        ((σ i * (t / w i)) ^ 2 / (1 - κ i * (t / w i))) :=
      Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (hRi i hi).2 (hw i hi).le
    _ = ∑ i ∈ s, σ i * S * t ^ 2 / (1 - K * t) := Finset.sum_congr rfl hterm
    _ = S * (S * t ^ 2 / (1 - K * t)) := by
      calc
        _ = ∑ i ∈ s, σ i * (S * t ^ 2 / (1 - K * t)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [← Finset.sum_mul]
    _ = (S * t) ^ 2 / (1 - K * t) := by ring

end StrongMixing
