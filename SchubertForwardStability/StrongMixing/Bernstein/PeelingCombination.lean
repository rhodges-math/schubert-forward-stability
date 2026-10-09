import SchubertForwardStability.StrongMixing.Bernstein.PeelingRows
import SchubertForwardStability.StrongMixing.Bernstein.PeelingRemainder
import SchubertForwardStability.StrongMixing.Bernstein.BernsteinCombination

/-!
# Finite Bernstein aggregation of deterministic peeling

Retained pieces and the final logarithmic residual form an exact finite sum.
The aggregation inequality, which holds for dependent pieces, combines their
explicit positive scales and denominator rates.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Each retained row and the final residual has its prescribed Bernstein scale and rate. -/
private theorem peeling_row_estimates (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : Finset ℤ) (hn : 4 ≤ A.card) (j : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hku : (if j < peelingLogDepth A.card then retainedRate c * M * Real.log A.card
      else remainderRate c * M) * u < 1) :
    let Z := fun ω => if j < peelingLogDepth A.card then ∑ i ∈ peelingPiece A j, X i ω
      else ∑ i ∈ peelingRemainder A (peelingLogDepth A.card), X i ω
    let σ := if j < peelingLogDepth A.card then peelingScale c M A.card j
      else M * Real.sqrt A.card * Real.sqrt (remainderVariance c)
    let κ := if j < peelingLogDepth A.card then retainedRate c * M * Real.log A.card
      else remainderRate c * M
    Integrable (fun ω => Real.exp (u * Z ω)) μ ∧
      Real.log (∫ ω, Real.exp (u * Z ω) ∂μ) ≤ (σ * u) ^ 2 / (1 - κ * u) := by
  dsimp only
  by_cases hj : j < peelingLogDepth A.card
  · simp only [ite_eq_left hj] at hku ⊢
    have hmax : max (A.card : ℝ) 2 = A.card :=
      max_eq_left (by exact_mod_cast (show 2 ≤ A.card by omega))
    simpa only [hmax] using
      peeling_row_bernstein_le μ X hX hcenter hM hc hbound hmix A j hu (by rwa [hmax])
  · simp only [ite_eq_right hj] at hku ⊢
    have h := peeling_residual_bernstein_le μ X hX hcenter hM hc hbound hmix A hn hu hku
    have he : (M * Real.sqrt A.card * Real.sqrt (remainderVariance c) * u) ^ 2 =
        A.card * (u * M) ^ 2 * remainderVariance c := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg A.card),
        Real.sq_sqrt (remainderVariance_pos hc).le]
      ring
    simpa only [he] using h

/-- The retained rows' constant rates and the residual rate sum to the explicit total rate. -/
private theorem peeling_rate_sum (J : ℕ) (c M : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (J + 1),
      if j < J then retainedRate c * M * Real.log n else remainderRate c * M) =
      (J : ℝ) * retainedRate c * M * Real.log n + remainderRate c * M := by
  rw [Finset.sum_range_succ]
  have he : (∑ j ∈ Finset.range J,
      if j < J then retainedRate c * M * Real.log n else remainderRate c * M) =
      ∑ _j ∈ Finset.range J, retainedRate c * M * Real.log n :=
    Finset.sum_congr rfl (fun j hj => ite_eq_left (Finset.mem_range.mp hj))
  rw [he]
  simp
  ring

/-- The retained geometric scales and the residual scale sum to the explicit total scale. -/
private theorem peeling_scale_sum (J : ℕ) (c M : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (J + 1), if j < J then peelingScale c M n j
      else M * Real.sqrt n * Real.sqrt (remainderVariance c)) =
      (∑ j ∈ Finset.range J, peelingScale c M n j) +
        M * Real.sqrt n * Real.sqrt (remainderVariance c) := by
  rw [Finset.sum_range_succ]
  have he : (∑ j ∈ Finset.range J, if j < J then peelingScale c M n j
      else M * Real.sqrt n * Real.sqrt (remainderVariance c)) =
      ∑ j ∈ Finset.range J, peelingScale c M n j :=
    Finset.sum_congr rfl (fun j hj => ite_eq_left (Finset.mem_range.mp hj))
  rw [he]
  simp

/-- The finite peeling pieces and the final residual combine into a Bernstein
bound. Its scale is the sum of the geometric retained scales plus the residual
scale, and its denominator rate is the sum of their explicit rates. -/
theorem peeling_combination_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c t : ℝ} (hM : 0 < M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : Finset ℤ) (hn : 4 ≤ A.card) (ht : 0 ≤ t)
    (hkt : ((peelingLogDepth A.card : ℝ) * retainedRate c * M * Real.log A.card +
      remainderRate c * M) * t < 1) :
    Integrable (fun ω => Real.exp (t * ∑ i ∈ A, X i ω)) μ ∧
      Real.log (∫ ω, Real.exp (t * ∑ i ∈ A, X i ω) ∂μ) ≤
        (((∑ j ∈ Finset.range (peelingLogDepth A.card), peelingScale c M A.card j) +
          M * Real.sqrt A.card * Real.sqrt (remainderVariance c)) * t) ^ 2 /
          (1 - ((peelingLogDepth A.card : ℝ) * retainedRate c * M * Real.log A.card +
            remainderRate c * M) * t) := by
  let J := peelingLogDepth A.card
  let R := peelingRemainder A J
  let Z (j : ℕ) (ω : Ω) :=
    if j < J then ∑ i ∈ peelingPiece A j, X i ω else ∑ i ∈ R, X i ω
  let σ (j : ℕ) :=
    if j < J then peelingScale c M A.card j
    else M * Real.sqrt A.card * Real.sqrt (remainderVariance c)
  let κ (j : ℕ) :=
    if j < J then retainedRate c * M * Real.log A.card else remainderRate c * M
  have hnp : 0 < A.card := by omega
  have hln : 0 < Real.log A.card := by linarith [(peeling_logs_pos A.card hn).1]
  have hZ : ∀ j ∈ Finset.range (J + 1), AEMeasurable (Z j) μ := by
    intro j _
    dsimp [Z]
    split <;> exact (Finset.measurable_sum _ (fun i _ => hX i)).aemeasurable
  have hσ : ∀ j ∈ Finset.range (J + 1), 0 < σ j := by
    intro j _
    dsimp [σ]
    split
    · exact peelingScale_pos hc hM hnp j
    · exact mul_pos (mul_pos hM (Real.sqrt_pos.mpr (by exact_mod_cast hnp)))
        (Real.sqrt_pos.mpr (remainderVariance_pos hc))
  have hκ : ∀ j ∈ Finset.range (J + 1), 0 ≤ κ j := by
    intro j _
    dsimp [κ]
    split
    · exact mul_nonneg (mul_nonneg (retainedRate_pos hc).le hM.le) hln.le
    · exact mul_nonneg (remainderRate_pos hc).le hM.le
  have hRow : ∀ j ∈ Finset.range (J + 1), ∀ u : ℝ, 0 ≤ u → κ j * u < 1 →
      Integrable (fun ω => Real.exp (u * Z j ω)) μ ∧
        Real.log (∫ ω, Real.exp (u * Z j ω) ∂μ) ≤ (σ j * u) ^ 2 / (1 - κ j * u) := by
    intro j _ u hu hku
    exact peeling_row_estimates μ X hX hcenter hM hc hbound hmix A hn j u hu hku
  have hκsum : (∑ j ∈ Finset.range (J + 1), κ j) =
      (J : ℝ) * retainedRate c * M * Real.log A.card + remainderRate c * M :=
    peeling_rate_sum J c M A.card
  have hσsum : (∑ j ∈ Finset.range (J + 1), σ j) =
      (∑ j ∈ Finset.range J, peelingScale c M A.card j) +
        M * Real.sqrt A.card * Real.sqrt (remainderVariance c) :=
    peeling_scale_sum J c M A.card
  have htot : (∑ j ∈ Finset.range (J + 1), κ j) * t < 1 := by rwa [hκsum]
  have h := log_laplace_sum_bernstein_le μ (Finset.range (J + 1))
    (by simp) Z hZ σ κ hσ hκ hRow t ht htot
  have hz (ω : Ω) : (∑ j ∈ Finset.range (J + 1), Z j ω) =
      ∑ i ∈ A, X i ω := by
    rw [Finset.sum_range_succ]
    have he : (∑ j ∈ Finset.range J, Z j ω) =
        ∑ j ∈ Finset.range J, ∑ i ∈ peelingPiece A j, X i ω :=
      Finset.sum_congr rfl (fun j hj => ite_eq_left (Finset.mem_range.mp hj))
    rw [he]
    simp only [Z, lt_self_iff_false, ite_false]
    exact (peeling_sum_decomposition A J (fun i => X i ω)).symm
  simpa only [hz, hκsum, hσsum] using h

end StrongMixing
