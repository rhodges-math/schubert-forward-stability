import SchubertForwardStability.StrongMixing.Bernstein.MPRPositive
import SchubertForwardStability.StrongMixing.Bernstein.LaplaceTail

/-!
# One-sided and two-sided MPR tails

The Laplace bound gives the upper tail. Applied to `-X` it gives the lower tail with the
same constant, and the union of the two events gives the two-sided bound with factor 2.

## References

* F. Merlevède, M. Peligrad and E. Rio, *Bernstein inequality and moderate deviations under
  strong mixing conditions*, High dimensional probability V: the Luminy volume, Inst. Math.
  Stat. (IMS) Collect. 5 (2009), 273-292, arXiv:1202.4777, Theorem 1 and (2.1).
-/

open MeasureTheory ProbabilityTheory

namespace StrongMixing

/-- The positive c-only tail coefficient is
`1/(4*peelingMprVariance(c)+2*peelingMprRate(c))`. -/
noncomputable def mprTailConstant (c : ℝ) : ℝ :=
  1 / (4 * peelingMprVariance c + 2 * peelingMprRate c)

/-- The explicit MPR tail coefficient is positive for every geometric rate `c>0`. -/
theorem mprTailConstant_pos {c : ℝ} (hc : 0 < c) : 0 < mprTailConstant c := by
  have h := peelingMprConstants_pos hc
  have hV := h.2
  have hR := h.1
  unfold mprTailConstant
  positivity

private theorem tail_fraction_le {V R a b x : ℝ} (hV : 0 < V) (hR : 0 < R)
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

/-- Upper tail of the Merlevède–Peligrad–Rio inequality. For a centered, AEMeasurable,
essentially bounded sequence indexed by the positive integers with `alpha(h) <= exp(-2*c*h)`,
the sum `S_k` of the first `k>=4` variables satisfies
`P(S_k >= x) <= exp(-K_c*x^2/(k*M^2+M*x*log(k)*log(log(k))))` for every `x>=0`, where
`K_c = mprTailConstant c` depends only on `c`. -/
theorem mpr_positive_upper_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ+ → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c x : ℝ} (hM : 0 ≤ M) (hc : 0 < c)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ (positiveExtension X 0) h ≤
      Real.exp (-2 * c * h)) (k : ℕ) (hk : 4 ≤ k) (hx : 0 ≤ x) :
    μ.real {ω | x ≤ positiveSum X k ω} ≤ Real.exp (-mprTailConstant c * x ^ 2 /
      ((k : ℝ) * M ^ 2 + M * x * Real.log k * Real.log (Real.log k))) := by
  by_cases hM0 : M = 0
  · simpa only [hM0, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, zero_add,
      div_zero, Real.exp_zero] using
      (measureReal_le_one : μ.real {ω | x ≤ positiveSum X k ω} ≤ 1)
  have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
  have hC := peelingMprConstants_pos hc
  have hV := hC.2
  have hR := hC.1
  have hln : 0 < Real.log k := by linarith [(peeling_logs_pos k hk).1]
  have hll := (peeling_logs_pos k hk).2
  let A := peelingMprVariance c * k * M ^ 2
  let B := peelingMprRate c * M * Real.log k * Real.log (Real.log k)
  have hA : 0 < A := by
    have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hLap : ∀ t : ℝ, 0 ≤ t → B * t < 1 →
      Integrable (fun ω => Real.exp (t * positiveSum X k ω)) μ ∧
        Real.log (∫ ω, Real.exp (t * positiveSum X k ω) ∂μ) ≤ A * t ^ 2 / (1 - B * t) := by
    intro t ht hBt
    have h := mpr_positive_laplace_le μ X hX hcenter hMp hc hbound hmix k hk ht hBt
    refine ⟨h.1, ?_⟩
    convert h.2 using 1
    dsimp [A, B]
    ring
  have h := measure_ge_of_log_laplace hA hB hLap hx
  have ha : (0 : ℝ) < k * M ^ 2 := by
    have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    positivity
  have hb : 0 ≤ M * x * Real.log k * Real.log (Real.log k) := by positivity
  have hf := tail_fraction_le (x := x) hC.2 hC.1 ha hb
  have hden : 4 * A + 2 * B * x =
      4 * peelingMprVariance c * ((k : ℝ) * M ^ 2) +
        2 * peelingMprRate c * (M * x * Real.log k * Real.log (Real.log k)) := by
    dsimp [A, B]
    ring
  refine h.trans (Real.exp_le_exp.mpr ?_)
  rw [hden]
  exact hf

/-- The lower tail satisfies the same bound as the upper tail:
`P(S_k <= -x) <= exp(-K_c*x^2/(k*M^2+M*x*log(k)*log(log(k))))` for every `k>=4`, `x>=0`
and `M>=0`. -/
theorem mpr_positive_lower_tail (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ+ → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c x : ℝ} (hM : 0 ≤ M) (hc : 0 < c)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ (positiveExtension X 0) h ≤
      Real.exp (-2 * c * h)) (k : ℕ) (hk : 4 ≤ k) (hx : 0 ≤ x) :
    μ.real {ω | positiveSum X k ω ≤ -x} ≤ Real.exp (-mprTailConstant c * x ^ 2 /
      ((k : ℝ) * M ^ 2 + M * x * Real.log k * Real.log (Real.log k))) := by
  let Y (i : ℕ+) (ω : Ω) := -X i ω
  have he : positiveExtension Y 0 = (fun i ω => -positiveExtension X 0 i ω) := by
    funext i ω
    by_cases hi : 0 < i <;> simp [positiveExtension, hi, Y]
  have hmixY (h : ℕ) (hh : 1 ≤ h) :
      mixingCoeff μ (positiveExtension Y 0) h ≤ Real.exp (-2 * c * h) := by
    rw [he]
    exact (mixingCoeff_comp_le μ (positiveExtension X 0) (fun z : ℝ => -z)
      measurable_neg h).trans (hmix h hh)
  have h := mpr_positive_upper_tail μ Y (fun i => (hX i).neg)
    (fun i => by simp only [Y, integral_neg, hcenter i, neg_zero]) hM hc
    (fun i => by simpa only [Y, abs_neg] using hbound i) hmixY k hk hx
  have hs (ω : Ω) : positiveSum Y k ω = -positiveSum X k ω := by simp [positiveSum, Y]
  have hE : {ω | x ≤ positiveSum Y k ω} = {ω | positiveSum X k ω ≤ -x} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hs]
    constructor <;> intro hh <;> linarith
  rw [hE] at h
  exact h

/-- The two-sided tail is at most twice the one-sided bound:
`P(|S_k| >= x) <= 2*exp(-K_c*x^2/(k*M^2+M*x*log(k)*log(log(k))))` for every `k>=4` and
`x>=0`, where `K_c` depends only on `c`. -/
theorem mpr_positive_two_sided (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ+ → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c x : ℝ} (hM : 0 ≤ M) (hc : 0 < c)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ (positiveExtension X 0) h ≤
      Real.exp (-2 * c * h)) (k : ℕ) (hk : 4 ≤ k) (hx : 0 ≤ x) :
    μ.real {ω | x ≤ |positiveSum X k ω|} ≤ 2 * Real.exp (-mprTailConstant c * x ^ 2 /
      ((k : ℝ) * M ^ 2 + M * x * Real.log k * Real.log (Real.log k))) := by
  have hU := mpr_positive_upper_tail μ X hX hcenter hM hc hbound hmix k hk hx
  have hL := mpr_positive_lower_tail μ X hX hcenter hM hc hbound hmix k hk hx
  have hE : {ω | x ≤ |positiveSum X k ω|} =
      {ω | x ≤ positiveSum X k ω} ∪ {ω | positiveSum X k ω ≤ -x} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    by_cases hp : 0 ≤ positiveSum X k ω
    · rw [abs_of_nonneg hp]
      constructor
      · exact Or.inl
      · rintro (hh | hh) <;> linarith
    · rw [abs_of_neg (lt_of_not_ge hp)]
      constructor
      · intro hh; right; linarith
      · rintro (hh | hh) <;> linarith
  rw [hE]
  exact (measureReal_union_le _ _).trans (by linarith only [hU, hL])

end StrongMixing
