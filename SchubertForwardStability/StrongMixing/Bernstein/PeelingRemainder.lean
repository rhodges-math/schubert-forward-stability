import SchubertForwardStability.StrongMixing.Inequalities.PeelingDepth
import SchubertForwardStability.StrongMixing.Inequalities.SubsetRemainder
import SchubertForwardStability.StrongMixing.Bernstein.RetainedBernstein

/-!
# Variance control of the final peeling residual

The logarithmic cutoff leaves at most `n/log(n)` coordinates. Combining this
cardinality bound with the transform estimate for arbitrary subsets gives
a c-only quadratic numerator of size `n`, without a remaining logarithm.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

/-- The c-only quadratic constant for the final logarithmic peeling residual is
`(retainedVariance(c)+2)/log(4)+3/(c*log(2))`. -/
noncomputable def remainderVariance (c : ℝ) : ℝ :=
  (retainedVariance c + 2) / Real.log 4 + 3 / (c * Real.log 2)

/-- The c-only denominator rate for the final peeling residual is `8+72/c`. -/
noncomputable def remainderRate (c : ℝ) : ℝ := 8 + 72 / c

/-- The final residual quadratic constant is strictly positive for `c>0`. -/
theorem remainderVariance_pos {c : ℝ} (hc : 0 < c) : 0 < remainderVariance c := by
  have hQ := retainedVariance_pos hc
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold remainderVariance
  positivity

/-- The final residual denominator rate is strictly positive for `c>0`. -/
theorem remainderRate_pos {c : ℝ} (hc : 0 < c) : 0 < remainderRate c := by
  unfold remainderRate
  positivity

/-- If `1<=m<=n/log(n)` and `n>=4`, the full remainder coefficient of cardinal
`m` is bounded by `n*remainderVariance(c)`. This removes the subset logarithm. -/
theorem remainder_size_bound {c : ℝ} (hc : 0 < c) (n m : ℕ) (hn : 4 ≤ n)
    (hm : (m : ℝ) ≤ (n : ℝ) / Real.log n) (hm1 : 1 ≤ m) :
    (m : ℝ) * (retainedVariance c + 2 + 3 * Real.log m / (c * Real.log 2)) ≤
      n * remainderVariance c := by
  have hln := (peeling_logs_pos n hn).1
  have hnp : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmp : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmln : (m : ℝ) * Real.log n ≤ n := (le_div_iff₀ (by linarith)).mp hm
  have hmn : (m : ℝ) ≤ n := by
    have h := mul_nonneg hmp (by linarith : 0 ≤ Real.log n - 1)
    nlinarith only [h, hmln]
  have hlm := Real.log_le_log (by exact_mod_cast (show 0 < m by omega)) hmn
  have hprod := (mul_le_mul_of_nonneg_left hlm hmp).trans hmln
  have hQ : 0 ≤ retainedVariance c + 2 := by linarith [retainedVariance_pos hc]
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4n := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    (show (4 : ℝ) ≤ n by exact_mod_cast hn)
  have hfirst : (m : ℝ) * (retainedVariance c + 2) ≤
      n * (retainedVariance c + 2) / Real.log 4 := by
    calc
      _ ≤ ((n : ℝ) / Real.log n) * (retainedVariance c + 2) :=
        mul_le_mul_of_nonneg_right hm hQ
      _ = ((n : ℝ) * (retainedVariance c + 2)) / Real.log n := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hnp hQ) hlog4 h4n
  have hlast : (m : ℝ) * (3 * Real.log m / (c * Real.log 2)) ≤
      n * (3 / (c * Real.log 2)) := by
    have h := mul_le_mul_of_nonneg_left hprod
      (by positivity : 0 ≤ 3 / (c * Real.log 2))
    convert h using 1 <;> ring
  calc
    _ = (m : ℝ) * (retainedVariance c + 2) +
        m * (3 * Real.log m / (c * Real.log 2)) := by ring
    _ ≤ n * (retainedVariance c + 2) / Real.log 4 +
        n * (3 / (c * Real.log 2)) := add_le_add hfirst hlast
    _ = _ := by unfold remainderVariance; ring

variable {Ω : Type*} [MeasurableSpace Ω]

/-- At the logarithmic cutoff, the final residual has an integrable exponential
transform and a Bernstein-shaped bound with numerator
`card(A)*(t*M)^2*remainderVariance(c)` and denominator `1-remainderRate(c)*M*t`.
The claim covers empty residuals and parameter zero. -/
theorem peeling_residual_bernstein_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c t : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : Finset ℤ) (hn : 4 ≤ A.card) (ht : 0 ≤ t)
    (hkt : remainderRate c * M * t < 1) :
    Integrable (fun ω => Real.exp (t *
      ∑ i ∈ peelingRemainder A (peelingLogDepth A.card), X i ω)) μ ∧
      Real.log (∫ ω, Real.exp (t *
        ∑ i ∈ peelingRemainder A (peelingLogDepth A.card), X i ω) ∂μ) ≤
          A.card * (t * M) ^ 2 * remainderVariance c / (1 - remainderRate c * M * t) := by
  let R := peelingRemainder A (peelingLogDepth A.card)
  have hmeas : Measurable (fun ω => ∑ i ∈ R, X i ω) :=
    Finset.measurable_sum _ (fun i _ => hX i)
  have hbd : ∀ ω, |∑ i ∈ R, X i ω| ≤ R.card * M := by
    intro ω
    calc
      _ ≤ ∑ i ∈ R, |X i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ R, M := Finset.sum_le_sum (fun i _ => hbound i ω)
      _ = _ := by simp
  refine ⟨integrable_exp_of_abs_le hmeas.aemeasurable (Filter.Eventually.of_forall hbd) t, ?_⟩
  have hκ : 0 ≤ remainderRate c * M * t :=
    mul_nonneg (mul_nonneg (remainderRate_pos hc).le hM.le) ht
  have hnum : 0 ≤ (A.card : ℝ) * (t * M) ^ 2 * remainderVariance c := by
    have hQ := remainderVariance_pos hc
    positivity
  have hden : 0 < 1 - remainderRate c * M * t := sub_pos.mpr hkt
  by_cases ht0 : t = 0
  · simp [ht0]
  by_cases hR : R.Nonempty
  · have hu : 0 ≤ t * M := mul_nonneg ht hM.le
    have hkt' : (8 + 72 / c) * (t * M) < 1 := by
      convert hkt using 1
      unfold remainderRate
      ring
    have hs : t * M ≤ 1 / 8 := by
      have hx := mul_nonneg (by positivity : 0 ≤ 72 / c) hu
      nlinarith only [hkt', hx]
    have hg : t * M ≤ c / 72 := by
      have hh : 72 / c * (t * M) < 1 := by nlinarith only [hkt', hu]
      have hh' : 72 * (t * M) / c < 1 := by
        convert hh using 1
        ring
      have hrel := (div_lt_one hc).mp hh'
      linarith
    have h := finite_set_remainder_laplace_le μ X hX hcenter hM hc hbound hmix
      R hR (lt_of_le_of_ne ht (Ne.symm ht0)) hs hg
    have hb := remainder_size_bound hc A.card R.card hn (peelingRemainder_log_card A hn)
      (by have hp := Finset.card_pos.mpr hR; omega)
    have hquad : Real.log (∫ ω, Real.exp (t * ∑ i ∈ R, X i ω) ∂μ) ≤
        A.card * (t * M) ^ 2 * remainderVariance c := by
      change _ ≤ R.card * (t * M) ^ 2 *
        (retainedVariance c + 2 + 3 * Real.log R.card / (c * Real.log 2)) at h
      have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg (t * M))
      refine h.trans ?_
      nlinarith only [hm]
    refine hquad.trans ?_
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hκ, mul_nonneg hnum hκ]
  · have hE : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
    change Real.log (∫ ω, Real.exp (t * ∑ i ∈ R, X i ω) ∂μ) ≤ _
    rw [hE]
    simp only [Finset.sum_empty, mul_zero, Real.exp_zero, integral_const,
      probReal_univ, one_smul, Real.log_one]
    exact div_nonneg hnum hden.le

end StrongMixing
