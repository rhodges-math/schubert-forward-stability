import SchubertForwardStability.StrongMixing.Bernstein.MPRTails

/-! # One-sided MPR tails for finite coordinate sets

The finite-set Laplace estimate yields the same one-sided Bernstein exponent
on every finite set of integer coordinates, and negation gives the lower tail.
The sequence need not be stationary.

## References

* F. Merlevède, M. Peligrad and E. Rio, *Bernstein inequality and moderate deviations under
  strong mixing conditions*, High dimensional probability V: the Luminy volume, Inst. Math.
  Stat. (IMS) Collect. 5 (2009), 273-292, arXiv:1202.4777, Theorem 1 and (2.1).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

private theorem finite_tail_fraction_le {V R a b x : ℝ} (hV : 0 < V) (hR : 0 < R)
    (ha : 0 < a) (hb : 0 ≤ b) :
    -x ^ 2 / (4 * V * a + 2 * R * b) ≤
      -(1 / (4 * V + 2 * R)) * x ^ 2 / (a + b) := by
  have hD : 0 < 4 * V * a + 2 * R * b := by positivity
  have hK : 0 < 4 * V + 2 * R := by positivity
  have hab : 0 < a + b := by positivity
  have hden : 4 * V * a + 2 * R * b ≤ (4 * V + 2 * R) * (a + b) := by
    nlinarith only [mul_nonneg hV.le hb, mul_nonneg hR.le ha.le]
  have hf := div_le_div_of_nonneg_left (sq_nonneg x) hD hden
  calc
    _ ≤ -(x ^ 2 / ((4 * V + 2 * R) * (a + b))) := by
      simpa only [neg_div] using neg_le_neg hf
    _ = _ := by field_simp

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A centered essentially bounded AEMeasurable integer family with geometric
mixing has the one-sided MPR upper tail on every finite coordinate set of
cardinality at least four. The coefficient depends only on `c`, the denominator
contains `log(k)*log(log(k))`, and `M=0` and `x=0` are included. -/
theorem mpr_finite_upper_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c x : ℝ} (hM : 0 ≤ M) (hc : 0 < c)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (S : Finset ℤ) (hk : 4 ≤ S.card) (hx : 0 ≤ x) :
    μ.real {ω | x ≤ ∑ i ∈ S, X i ω} ≤ Real.exp (-mprTailConstant c * x ^ 2 /
      ((S.card : ℝ) * M ^ 2 + M * x * Real.log S.card * Real.log (Real.log S.card))) := by
  by_cases hM0 : M = 0
  · simpa only [hM0, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, zero_add,
      div_zero, Real.exp_zero] using
      (measureReal_le_one : μ.real {ω | x ≤ ∑ i ∈ S, X i ω} ≤ 1)
  have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
  have hC := peelingMprConstants_pos hc
  have hln : 0 < Real.log S.card := by linarith [(peeling_logs_pos S.card hk).1]
  have hll := (peeling_logs_pos S.card hk).2
  let A := peelingMprVariance c * S.card * M ^ 2
  let B := peelingMprRate c * M * Real.log S.card * Real.log (Real.log S.card)
  have hA : 0 < A := by
    have hkp : (0 : ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
    have hV := hC.2
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    have hR := hC.1
    dsimp [B]
    positivity
  have hLap : ∀ t : ℝ, 0 ≤ t → B * t < 1 →
      Integrable (fun ω => Real.exp (t * ∑ i ∈ S, X i ω)) μ ∧
        Real.log (∫ ω, Real.exp (t * ∑ i ∈ S, X i ω) ∂μ) ≤ A * t ^ 2 / (1 - B * t) := by
    intro t ht hBt
    have h := mpr_laplace_ae_le μ X hX hcenter hMp hc hbound hmix S hk ht hBt
    refine ⟨h.1, ?_⟩
    convert h.2 using 1
    dsimp [A, B]
    ring
  have h := measure_ge_of_log_laplace hA hB hLap hx
  have ha : (0 : ℝ) < S.card * M ^ 2 := by
    have hkp : (0 : ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
    positivity
  have hb : 0 ≤ M * x * Real.log S.card * Real.log (Real.log S.card) := by positivity
  have hf := finite_tail_fraction_le (x := x) hC.2 hC.1 ha hb
  have hden : 4 * A + 2 * B * x =
      4 * peelingMprVariance c * ((S.card : ℝ) * M ^ 2) +
        2 * peelingMprRate c * (M * x * Real.log S.card * Real.log (Real.log S.card)) := by
    dsimp [A, B]
    ring
  refine h.trans (Real.exp_le_exp.mpr ?_)
  rw [hden]
  exact hf

/-- On every finite set of at least four integer coordinates, the lower tail satisfies
the same bound as the upper tail, with the same constant depending only on `c`.
The coordinates are AEMeasurable and essentially bounded, the sequence need not be
stationary, and the bound holds for all `M>=0` and `x>=0`. -/
theorem mpr_finite_lower_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c x : ℝ} (hM : 0 ≤ M) (hc : 0 < c)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (S : Finset ℤ) (hk : 4 ≤ S.card) (hx : 0 ≤ x) :
    μ.real {ω | (∑ i ∈ S, X i ω) ≤ -x} ≤ Real.exp (-mprTailConstant c * x ^ 2 /
      ((S.card : ℝ) * M ^ 2 + M * x * Real.log S.card * Real.log (Real.log S.card))) := by
  let Y (i : ℤ) (ω : Ω) := -X i ω
  have hmixY (h : ℕ) (hh : 1 ≤ h) :
      mixingCoeff μ Y h ≤ Real.exp (-2 * c * h) :=
    (mixingCoeff_comp_le μ X (fun z : ℝ => -z) measurable_neg h).trans (hmix h hh)
  have h := mpr_finite_upper_tail μ Y (fun i => (hX i).neg)
    (fun i => by simp only [Y, integral_neg, hcenter i, neg_zero]) hM hc
    (fun i => by simpa only [Y, abs_neg] using hbound i) hmixY S hk hx
  have hs (ω : Ω) : (∑ i ∈ S, Y i ω) = -(∑ i ∈ S, X i ω) := by simp [Y]
  have hE : {ω | x ≤ ∑ i ∈ S, Y i ω} = {ω | (∑ i ∈ S, X i ω) ≤ -x} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hs]
    constructor <;> intro hh <;> linarith
  rw [hE] at h
  exact h

end StrongMixing
