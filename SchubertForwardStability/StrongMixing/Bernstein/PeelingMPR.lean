import SchubertForwardStability.StrongMixing.Bernstein.PeelingCombination
import SchubertForwardStability.StrongMixing.Bernstein.PeelingConstants

/-!
# The logarithmic peeling Laplace bound

The finite retained-piece scales have a uniformly bounded geometric sum. The
logarithmic cutoff bounds the total denominator rate, giving the
`log(n)*log(log(n))` Bernstein denominator with constants depending only on `c`.

## References

* F. Merlevède, M. Peligrad and E. Rio, *Bernstein inequality and moderate deviations under
  strong mixing conditions*, High dimensional probability V: the Luminy volume, Inst. Math.
  Stat. (IMS) Collect. 5 (2009), 273-292, arXiv:1202.4777, Theorem 1 and (2.1).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A centered measurable pointwise bounded geometrically mixing sequence has
the MPR logarithmic Laplace bound on every finite coordinate set of size `n` at
least four. Both positive constants are the explicit c-only peeling constants,
and the denominator is `1-R_c*M*log(n)*log(log(n))*t`. -/
theorem peeling_mpr_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c t : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : Finset ℤ) (hn : 4 ≤ A.card) (ht : 0 ≤ t)
    (hkt : peelingMprRate c * M * Real.log A.card * Real.log (Real.log A.card) * t < 1) :
    Integrable (fun ω => Real.exp (t * ∑ i ∈ A, X i ω)) μ ∧
      Real.log (∫ ω, Real.exp (t * ∑ i ∈ A, X i ω) ∂μ) ≤
        A.card * (t * M) ^ 2 * peelingMprVariance c /
          (1 - peelingMprRate c * M * Real.log A.card * Real.log (Real.log A.card) * t) := by
  let J := peelingLogDepth A.card
  let K := (J : ℝ) * retainedRate c * M * Real.log A.card + remainderRate c * M
  let S := (∑ j ∈ Finset.range J, peelingScale c M A.card j) +
    M * Real.sqrt A.card * Real.sqrt (remainderVariance c)
  have hln : 0 < Real.log A.card := by linarith [(peeling_logs_pos A.card hn).1]
  have hP := peelingTotalRate_pos hc
  have hb := peelingRate_bounds hc A.card hn
  have hret := mul_le_mul_of_nonneg_right hb.1 (mul_nonneg hM.le hln.le)
  have hjret := mul_le_mul_of_nonneg_left hret (Nat.cast_nonneg J : 0 ≤ (J : ℝ))
  have hrem := mul_le_mul_of_nonneg_right hb.2 hM.le
  have hcount := peelingLogDepth_count_le A.card hn
  have hcount' := mul_le_mul_of_nonneg_right hcount
    (mul_nonneg (mul_nonneg hP.le hM.le) hln.le)
  have hK : K ≤ peelingMprRate c * M * Real.log A.card * Real.log (Real.log A.card) := by
    calc
      K ≤ ((J : ℝ) + 1) * (peelingTotalRate c * M * Real.log A.card) := by
        dsimp [K]
        nlinarith only [hjret, hrem]
      _ ≤ (1 / Real.log 2 + 2 / Real.log (Real.log 4)) * Real.log (Real.log A.card) *
          (peelingTotalRate c * M * Real.log A.card) := hcount'
      _ = _ := by unfold peelingMprRate; ring
  have hKt := (mul_le_mul_of_nonneg_right hK ht).trans_lt hkt
  have h := peeling_combination_le μ X hX hcenter hM hc hbound hmix A hn ht hKt
  have hscale := peelingScale_sum_le (c := c) hM.le A.card J
  have hS : S ≤ M * Real.sqrt A.card *
      (Real.sqrt (retainedVariance c) / (1 - Real.sqrt (1 / 2)) +
        Real.sqrt (remainderVariance c)) := by
    calc
      S ≤ M * Real.sqrt A.card * Real.sqrt (retainedVariance c) /
          (1 - Real.sqrt (1 / 2)) + M * Real.sqrt A.card *
            Real.sqrt (remainderVariance c) := add_le_add hscale le_rfl
      _ = _ := by ring
  have hnp : 0 < A.card := by omega
  have hSp : 0 ≤ S := by
    have hsum : 0 ≤ ∑ j ∈ Finset.range J, peelingScale c M A.card j :=
      Finset.sum_nonneg (fun j _ => (peelingScale_pos hc hM hnp j).le)
    dsimp [S]
    positivity
  have hnum : (S * t) ^ 2 ≤ A.card * (t * M) ^ 2 * peelingMprVariance c := by
    have hsquare := mul_self_le_mul_self (mul_nonneg hSp ht)
      (mul_le_mul_of_nonneg_right hS ht)
    have he : (M * Real.sqrt A.card *
        (Real.sqrt (retainedVariance c) / (1 - Real.sqrt (1 / 2)) +
          Real.sqrt (remainderVariance c)) * t) ^ 2 =
          A.card * (t * M) ^ 2 * peelingMprVariance c := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg A.card)]
      unfold peelingMprVariance
      ring
    rw [← he]
    simpa only [sq] using hsquare
  refine ⟨h.1, h.2.trans ?_⟩
  change (S * t) ^ 2 / (1 - K * t) ≤ _
  calc
    _ ≤ A.card * (t * M) ^ 2 * peelingMprVariance c / (1 - K * t) :=
      div_le_div_of_nonneg_right hnum (sub_pos.mpr hKt).le
    _ ≤ _ := div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
        (peelingMprConstants_pos hc).2.le)
      (sub_pos.mpr hkt) (by nlinarith only [mul_le_mul_of_nonneg_right hK ht])

end StrongMixing
