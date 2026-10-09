import SchubertForwardStability.StrongMixing.Inequalities.Laplace.IbragimovProducts
import SchubertForwardStability.StrongMixing.Inequalities.Laplace.LaplaceLogs
import SchubertForwardStability.StrongMixing.Inequalities.Laplace.BoundedLaplace

/-!
# Log-Laplace decoupling of finite centered block products

The finite Ibragimov discrepancy controls the difference between a joint
Laplace transform and the product of block transforms. Centering gives a product
of transforms at least one, allowing the scalar logarithmic comparison.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A finite family of centered bounded blocks has joint log-Laplace transform at
most the sum of its block transforms and the explicit Ibragimov error
`(p-1)*a*exp(|t|*sum M)`. The hypothesis bounds only the defined prefix/future
sigma-field coefficients. Blocks need not be independent, and `p = 0` is allowed. -/
theorem block_product_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) (M : ℕ → ℝ)
    (hbound : ∀ i ω, |Z i ω| ≤ M i)
    (hcenter : ∀ i, ∫ ω, Z i ω ∂μ = 0) {a : ℝ} (ha : 0 ≤ a) (p : ℕ)
    (hcut : ∀ k, 1 ≤ k → k < p →
      strongMixingCoeff μ (generatedSigma Z {i | i < k})
        (generatedSigma Z {i | k ≤ i ∧ i < p}) ≤ a) (t : ℝ) :
    Real.log (∫ ω, Real.exp (t * ∑ i ∈ Finset.range p, Z i ω) ∂μ) ≤
      (∑ i ∈ Finset.range p, Real.log (∫ ω, Real.exp (t * Z i ω) ∂μ)) +
        ((p - 1 : ℕ) : ℝ) * a * Real.exp (|t| * ∑ i ∈ Finset.range p, M i) := by
  let W : ℕ → Ω → ℝ := fun i ω => Real.exp (t * Z i ω)
  have hw : ∀ i, Measurable (W i) := fun i => (hZ i).const_mul t |>.exp
  have hi (i : ℕ) : Integrable (Z i) μ :=
    (MemLp.of_bound (p := 1) (hZ i).aestronglyMeasurable (M i)
      (Filter.Eventually.of_forall (fun ω => by simpa using hbound i ω))).integrable le_rfl
  have he (i : ℕ) : Integrable (W i) μ :=
    integrable_exp_of_abs_le (μ := μ) (hZ i).aemeasurable
      (Filter.Eventually.of_forall (hbound i)) t
  have he1 (i : ℕ) : 1 ≤ ∫ ω, W i ω ∂μ :=
    one_le_integral_exp_centered μ (Z i) (hi i) t (he i) (hcenter i)
  have hb (i : ℕ) (ω : Ω) : W i ω ≤ Real.exp (|t| * M i) := by
    apply Real.exp_le_exp.mpr
    calc
      t * Z i ω ≤ |t * Z i ω| := le_abs_self _
      _ = |t| * |Z i ω| := abs_mul _ _
      _ ≤ |t| * M i := mul_le_mul_of_nonneg_left (hbound i ω) (abs_nonneg _)
  have hcw : ∀ k, 1 ≤ k → k < p →
      strongMixingCoeff μ (generatedSigma W {i | i < k})
        (generatedSigma W {i | k ≤ i ∧ i < p}) ≤ a := by
    intro k hk hkp
    have hg : Measurable (fun x : ℝ => Real.exp (t * x)) := by fun_prop
    exact (strongMixingCoeff_mono μ
      (generatedSigma_comp_le Z _ hg _) (generatedSigma_comp_le Z _ hg _)).trans
        (hcut k hk hkp)
  have herr := nonnegative_product_error_le μ W hw (fun i => Real.exp (|t| * M i))
    (fun _ => (Real.exp_pos _).le) (fun _ _ => (Real.exp_pos _).le) hb ha p hcw
  have hprod (ω : Ω) : (∏ i ∈ Finset.range p, W i ω) =
      Real.exp (t * ∑ i ∈ Finset.range p, Z i ω) := by
    simp only [W, Finset.mul_sum, Real.exp_sum]
  have hboundSum (ω : Ω) : |∑ i ∈ Finset.range p, Z i ω| ≤
      ∑ i ∈ Finset.range p, M i :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => hbound i ω))
  have hsumE : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range p, Z i ω)) μ :=
    integrable_exp_of_abs_le (μ := μ)
      (Finset.measurable_sum (Finset.range p) (fun i _ => hZ i)).aemeasurable
      (Filter.Eventually.of_forall hboundSum) t
  have hP1 : 1 ≤ ∏ i ∈ Finset.range p, (∫ ω, W i ω ∂μ) := by
    simpa only [Finset.prod_const_one] using
      Finset.prod_le_prod₀ (s := Finset.range p) (f := fun _ => (1 : ℝ))
        (fun _ _ => zero_le_one) (fun i _ => he1 i)
  have hlog := log_le_log_add_abs (integral_exp_pos hsumE) hP1
  simp_rw [hprod] at herr
  have hlogP : Real.log (∏ i ∈ Finset.range p, (∫ ω, W i ω ∂μ)) =
      ∑ i ∈ Finset.range p, Real.log (∫ ω, W i ω ∂μ) :=
    Real.log_prod (fun i _ => (lt_of_lt_of_le zero_lt_one (he1 i)).ne')
  have hprodM : (∏ i ∈ Finset.range p, Real.exp (|t| * M i)) =
      Real.exp (|t| * ∑ i ∈ Finset.range p, M i) := by
    rw [← Real.exp_sum, ← Finset.mul_sum]
  rw [hlogP] at hlog
  rw [hprodM] at herr
  exact hlog.trans (add_le_add le_rfl herr)

end StrongMixing
