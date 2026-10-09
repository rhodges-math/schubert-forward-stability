/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The bounded-Lipschitz argument is adapted from Mathlib's ConvergenceInDistribution.
-/
import SchubertForwardStability.LimitTheorems.Convergence.Probability

/-! # Slutsky's theorem on varying probability spaces

Adapted from Mathlib's `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean` at
commit `b2bf051` (Rémy Degenne, Apache License 2.0); modified to allow the random variables
of the sequence to live on probability spaces that vary with the index, with the
bounded-Lipschitz estimate applied on each of these spaces.

## Main statements

* `tendstoInDistribution_of_sub`: perturbations vanishing in probability preserve weak limits.
* `slutsky_prod`: joint convergence with a coordinate tending to a constant.
* `slutsky_add`, `slutsky_mul`: sum and product forms of Slutsky's theorem.

## Implementation notes

The bounded-Lipschitz integral estimate is applied separately to each source measure.
No common source space is required. The convergence filter is countably generated.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace LimitTheorems

variable {ι E Ω' : Type*} {Ω : ι → Type*}
  [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
  [∀ i, IsProbabilityMeasure (μ i)] [MeasurableSpace Ω']
  {μ' : Measure Ω'} [IsProbabilityMeasure μ'] [MeasurableSpace E]
  [SeminormedAddCommGroup E] [SecondCountableTopology E] [BorelSpace E]
  {X Y : (i : ι) → Ω i → E} {Z : Ω' → E} {l : Filter ι} [l.IsCountablyGenerated]

/-- Bounded Lipschitz tests compare mapped integrals by a small perturbation
radius and the probability of its complementary norm event. -/
private theorem lipschitz_integral_compare {Ω'' : Type*} [MeasurableSpace Ω'']
    {ν : Measure Ω''} [IsProbabilityMeasure ν] {f g : Ω'' → E}
    (hf : AEMeasurable f ν) (hg : AEMeasurable g ν) {F : E → ℝ} {M : ℝ} {L : NNReal}
    (hF_bounded : ∀ x y, dist (F x) (F y) ≤ M) (hF_lip : LipschitzWith L F)
    {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    |∫ ω, F ω ∂ν.map g - C| ≤ L * (ε / 2) +
      M * ν.real {ω | ε / 2 ≤ ‖g ω - f ω‖} + |∫ ω, F ω ∂ν.map f - C| := by
  have hF_cont : Continuous F := hF_lip.continuous
  refine (abs_sub_le (∫ ω, F ω ∂ν.map g) (∫ ω, F ω ∂ν.map f) C).trans ?_
  gcongr
  have h_int_g : Integrable (fun x ↦ F (g x)) ν := by
    refine Integrable.of_bound (by fun_prop) (‖F 0‖ + M) (ae_of_all _ fun a ↦ ?_)
    rw [← sub_le_iff_le_add']
    exact (abs_sub_abs_le_abs_sub (F (g a)) (F 0)).trans (hF_bounded _ _)
  have h_int_f : Integrable (fun x ↦ F (f x)) ν := by
    refine Integrable.of_bound (by fun_prop) (‖F 0‖ + M) (ae_of_all _ fun a ↦ ?_)
    rw [← sub_le_iff_le_add']
    exact (abs_sub_abs_le_abs_sub (F (f a)) (F 0)).trans (hF_bounded _ _)
  have h_int_sub : Integrable (fun a ↦ ‖F (g a) - F (f a)‖) ν := by
    rw [integrable_norm_iff (by fun_prop)]
    exact h_int_g.sub h_int_f
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by fun_prop), ← integral_sub h_int_g h_int_f,
    ← Real.norm_eq_abs]
  calc
    ‖∫ a, F (g a) - F (f a) ∂ν‖ ≤ ∫ a, ‖F (g a) - F (f a)‖ ∂ν :=
      norm_integral_le_integral_norm _
    _ = ∫ a in {x | ‖g x - f x‖ < ε / 2}, ‖F (g a) - F (f a)‖ ∂ν +
        ∫ a in {x | ε / 2 ≤ ‖g x - f x‖}, ‖F (g a) - F (f a)‖ ∂ν := by
      symm
      simp_rw [← not_lt]
      exact integral_add_compl₀ (nullMeasurableSet_lt (by fun_prop) (by fun_prop)) h_int_sub
    _ ≤ ∫ a in {x | ‖g x - f x‖ < ε / 2}, L * (ε / 2) ∂ν +
        ∫ a in {x | ε / 2 ≤ ‖g x - f x‖}, M ∂ν := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
        · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
        · exact fun x hx ↦ hF_lip.norm_sub_le_of_le hx.le
      · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a ↦ ?_
        rw [← dist_eq_norm]
        exact hF_bounded _ _
    _ = L * (ε / 2) * ν.real {x | ‖g x - f x‖ < ε / 2} +
        M * ν.real {ω | ε / 2 ≤ ‖g ω - f ω‖} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
        Set.univ_inter, smul_eq_mul]
      ring
    _ ≤ L * (ε / 2) + M * ν.real {ω | ε / 2 ≤ ‖g ω - f ω‖} := by
      rw [mul_assoc]
      gcongr
      grw [measureReal_le_one, mul_one]

/-- A perturbation tending to zero in probability preserves convergence in distribution. -/
theorem tendstoInDistribution_of_sub (hXZ : TendstoInDistribution X l Z μ μ')
    (hXY : TendstoInProbability (fun i ω ↦ Y i ω - X i ω) l 0 μ)
    (hY : ∀ i, AEMeasurable (Y i) (μ i)) : TendstoInDistribution Y l Z μ μ' := by
  have hZ := hXZ.aemeasurable_limit
  have hX := hXZ.forall_aemeasurable
  refine ⟨hY, hZ, ?_⟩
  refine (tendsto_iff_forall_lipschitz_integral_tendsto
    (μs := fun n ↦ (⟨(μ n).map (Y n), inferInstance⟩ : ProbabilityMeasure E))
    (μ := (⟨μ'.map Z, inferInstance⟩ : ProbabilityMeasure E))).mpr ?_
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  simp only [ProbabilityMeasure.coe_mk]
  have hF_cont : Continuous F := hF_lip.continuous
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip (0 : E)
    simp only [← hF_lip, integral_const, smul_eq_mul]
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ι ↦ F 0) l (𝓝 (F 0)))
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in l,
      |∫ ω, F ω ∂(μ n).map (Y n) - ∫ ω, F ω ∂μ'.map Z| < L * ε by
    intro ε hε
    convert this (ε / L) (by positivity) using 1
    field_simp
  intro ε hε
  have h_le n : |∫ ω, F ω ∂(μ n).map (Y n) - ∫ ω, F ω ∂μ'.map Z| ≤
      L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖} +
        |∫ ω, F ω ∂(μ n).map (X n) - ∫ ω, F ω ∂μ'.map Z| :=
    lipschitz_integral_compare (hX n) (hY n) hF_bounded hF_lip hε _
  have h_tendsto : Tendsto (fun n ↦ L * (ε / 2) +
      M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖} +
      |∫ ω, F ω ∂(μ n).map (X n) - ∫ ω, F ω ∂μ'.map Z|) l (𝓝 (L * ε / 2)) := by
    have h_prob := hXY.measure_ge (show 0 < ε / 2 by positivity)
    simp only [sub_zero] at h_prob
    have h_int := (tendsto_iff_forall_lipschitz_integral_tendsto.mp hXZ.tendsto)
      F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
    have h_abs := (h_int.sub_const (∫ ω, F ω ∂μ'.map Z)).abs
    have h_const : Tendsto (fun _ : ι ↦ (L : ℝ) * (ε / 2)) l (𝓝 (L * (ε / 2))) :=
      tendsto_const_nhds
    simpa [mul_div_assoc, ProbabilityMeasure.coe_mk] using
      ((h_const.add (h_prob.const_mul M)).add h_abs)
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn

/-- Slutsky's theorem for a pair with one coordinate converging in probability to a constant. -/
theorem slutsky_prod {E' : Type*} [MeasurableSpace E'] [SeminormedAddCommGroup E']
    [SecondCountableTopology E'] [BorelSpace E'] {Y : (i : ι) → Ω i → E'} {c : E'}
    (hXZ : TendstoInDistribution X l Z μ μ') (hY : TendstoInProbability Y l c μ)
    (hYm : ∀ i, AEMeasurable (Y i) (μ i)) :
    TendstoInDistribution (fun i ω ↦ (X i ω, Y i ω)) l (fun ω ↦ (Z ω, c)) μ μ' := by
  apply tendstoInDistribution_of_sub (X := fun i ω ↦ (X i ω, c))
    (hXZ.continuous_comp (g := fun x ↦ (x, c)) (by fun_prop))
  · have h := (tendstoInProbability_sub_const.mpr hY).prod_zero (E := E)
    simpa only [Prod.mk_sub_mk, sub_self] using h
  · exact fun i ↦ (hXZ.forall_aemeasurable i).prodMk (hYm i)

/-- Applying a continuous map to a Slutsky pair preserves the joint limit. -/
theorem slutsky_continuous {E' F : Type*} [MeasurableSpace E']
    [SeminormedAddCommGroup E'] [SecondCountableTopology E'] [BorelSpace E']
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    {Y : (i : ι) → Ω i → E'} {c : E'} {g : E × E' → F} (hg : Continuous g)
    (hXZ : TendstoInDistribution X l Z μ μ') (hY : TendstoInProbability Y l c μ)
    (hYm : ∀ i, AEMeasurable (Y i) (μ i)) :
    TendstoInDistribution (fun i ω ↦ g (X i ω, Y i ω)) l (fun ω ↦ g (Z ω, c)) μ μ' :=
  (slutsky_prod hXZ hY hYm).continuous_comp hg

/-- The sum form of Slutsky's theorem on varying source spaces. -/
theorem slutsky_add {c : E} (hXZ : TendstoInDistribution X l Z μ μ')
    (hY : TendstoInProbability Y l c μ) (hYm : ∀ i, AEMeasurable (Y i) (μ i)) :
    TendstoInDistribution (fun i ω ↦ X i ω + Y i ω) l (fun ω ↦ Z ω + c) μ μ' :=
  slutsky_continuous (g := fun p ↦ p.1 + p.2) (by fun_prop) hXZ hY hYm

/-- The product form of Slutsky's theorem for real random variables on varying source spaces. -/
theorem slutsky_mul {X Y : (i : ι) → Ω i → ℝ} {Z : Ω' → ℝ} {c : ℝ}
    (hXZ : TendstoInDistribution X l Z μ μ') (hY : TendstoInProbability Y l c μ)
    (hYm : ∀ i, AEMeasurable (Y i) (μ i)) :
    TendstoInDistribution (fun i ω ↦ X i ω * Y i ω) l (fun ω ↦ Z ω * c) μ μ' :=
  slutsky_continuous (g := fun p ↦ p.1 * p.2) (by fun_prop) hXZ hY hYm

end LimitTheorems
