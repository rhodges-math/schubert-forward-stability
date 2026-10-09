import SchubertForwardStability.StrongMixing.Inequalities.RetainedLaplace

/-!
# Bernstein-shaped control of deterministic retained subsets

The retained quadratic transform estimate is put into a form usable by the
finite Bernstein aggregation inequality. The constants depend only on
the geometric mixing rate, and the logarithmic parameter is explicit.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

/-- The quadratic constant for a retained set under geometric rate `c`, namely
`6*(1+8*exp(-2*c)/(1-exp(-2*c)))+384/c^2`. Estimates require `c>0`. -/
noncomputable def retainedVariance (c : ℝ) : ℝ :=
  6 * (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) + 384 / c ^ 2

/-- The denominator rate for retained Bernstein bounds, depending only on the
geometric coefficient rate: `192/log(2)+6/(c*log(2))`. -/
noncomputable def retainedRate (c : ℝ) : ℝ := 192 / Real.log 2 + 6 / (c * Real.log 2)

/-- The retained quadratic constant is strictly positive at every positive
geometric rate, including arbitrarily small rates. -/
theorem retainedVariance_pos {c : ℝ} (hc : 0 < c) : 0 < retainedVariance c := by
  have he : Real.exp (-2 * c) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  unfold retainedVariance
  positivity

/-- The retained denominator rate is strictly positive at every positive
geometric rate. -/
theorem retainedRate_pos {c : ℝ} (hc : 0 < c) : 0 < retainedRate c := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold retainedRate
  positivity

/-- For any logarithmic size `L>=log(2)`, a retained Bernstein parameter with
`rate(c)*M*L*t<1` satisfies both smallness gates of the retained quadratic estimate. -/
theorem retainedRate_small {c M L t : ℝ} (hc : 0 < c) (hM : 0 < M)
    (hL : Real.log 2 ≤ L) (ht : 0 ≤ t)
    (hkt : retainedRate c * M * L * t < 1) :
    t * M ≤ 1 / 192 ∧ t * M ≤ c * Real.log 2 / (6 * L) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLp : 0 < L := h2.trans_le hL
  let u := t * M
  have hu : 0 ≤ u := mul_nonneg ht hM.le
  have hku : retainedRate c * L * u < 1 := by
    convert hkt using 1
    dsimp [u]
    ring
  have ha : 192 / Real.log 2 * Real.log 2 = (192 : ℝ) := by field_simp
  have ham := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 192 / Real.log 2)
  have hb : 0 ≤ 6 / (c * Real.log 2) * L := by positivity
  have hs : 192 ≤ retainedRate c * L := by
    unfold retainedRate
    nlinarith only [ha, ham, hb]
  have hs' : 192 * u < 1 :=
    (mul_le_mul_of_nonneg_right hs hu).trans_lt hku
  have ha' : 0 ≤ 192 / Real.log 2 * L := by positivity
  have hg : 6 / (c * Real.log 2) * L ≤ retainedRate c * L := by
    unfold retainedRate
    nlinarith only [ha']
  have hg' : (6 * L * u) / (c * Real.log 2) < 1 := by
    have h := (mul_le_mul_of_nonneg_right hg hu).trans_lt hku
    convert h using 1
    ring
  have hrel : 6 * L * u < c * Real.log 2 :=
    (div_lt_one (mul_pos hc h2)).mp hg'
  refine ⟨by change u ≤ 1 / 192; linarith, ?_⟩
  change u ≤ c * Real.log 2 / (6 * L)
  apply (le_div_iff₀ (by positivity : 0 < 6 * L)).mpr
  nlinarith only [hrel]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A retained subset has an integrable exponential transform and a
Bernstein-shaped log-Laplace bound with variance numerator
`card(A)*(t*M)^2*retainedVariance(c)` and denominator
`1-retainedRate(c)*M*log(max(card(A),2))*t`. -/
theorem retained_subset_bernstein_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c t : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : Finset ℤ) (ht : 0 ≤ t)
    (hkt : retainedRate c * M * Real.log (max (A.card : ℝ) 2) * t < 1) :
    Integrable (fun ω => Real.exp (t * ∑ i ∈ retainedSubset A, X i ω)) μ ∧
      Real.log (∫ ω, Real.exp (t * ∑ i ∈ retainedSubset A, X i ω) ∂μ) ≤
        A.card * (t * M) ^ 2 * retainedVariance c /
          (1 - retainedRate c * M * Real.log (max (A.card : ℝ) 2) * t) := by
  have hmeas : Measurable (fun ω => ∑ i ∈ retainedSubset A, X i ω) :=
    Finset.measurable_sum _ (fun i _ => hX i)
  have hbd : ∀ ω, |∑ i ∈ retainedSubset A, X i ω| ≤ (retainedSubset A).card * M := by
    intro ω
    calc
      _ ≤ ∑ i ∈ retainedSubset A, |X i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ retainedSubset A, M := Finset.sum_le_sum (fun i _ => hbound i ω)
      _ = _ := by simp
  refine ⟨integrable_exp_of_abs_le hmeas.aemeasurable (Filter.Eventually.of_forall hbd) t, ?_⟩
  by_cases ht0 : t = 0
  · simp [ht0]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have h2 : Real.log 2 ≤ Real.log (max (A.card : ℝ) 2) :=
    Real.log_le_log (by norm_num) (le_max_right _ _)
  have hs := retainedRate_small hc hM h2 ht hkt
  have hq := retained_subset_quadratic_le μ X hX hcenter hM hc hbound hmix A htpos hs.1 hs.2
  have hκ : 0 ≤ retainedRate c * M * Real.log (max (A.card : ℝ) 2) * t := by
    have hlog : 0 < Real.log (max (A.card : ℝ) 2) :=
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le h2
    exact mul_nonneg (mul_nonneg (mul_nonneg (retainedRate_pos hc).le hM.le) hlog.le) ht
  change _ ≤ A.card * (t * M) ^ 2 * retainedVariance c at hq
  refine hq.trans ?_
  apply (le_div_iff₀ (sub_pos.mpr hkt)).mpr
  have hnum : 0 ≤ (A.card : ℝ) * (t * M) ^ 2 * retainedVariance c :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (retainedVariance_pos hc).le
  nlinarith only [hκ, mul_nonneg hnum hκ]

end StrongMixing
