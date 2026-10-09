import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorQuadratic

/-!
# Laplace comparison after deleting coordinates

Uniformly bounded deleted coordinates give an explicit deterministic Laplace
penalty. Rounded Cantor retention turns it into the stated depth and parity-loss
terms, including empty intervals.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- If `A` is contained in a finite coordinate set `B`, deleting `B` minus `A`
increases the upper log-Laplace bound by at most `t*M*card(B minus A)` for `t >= 0`
and measurable coordinates uniformly bounded in absolute value by `M`.
No centering, mixing, or independence hypothesis is required. -/
theorem removed_coordinates_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) {M t : ℝ}
    (hbound : ∀ i ω, |X i ω| ≤ M) (ht : 0 ≤ t) (A B : Finset ℤ) (hA : A ⊆ B) :
    Real.log (∫ ω, Real.exp (t * ∑ i ∈ B, X i ω) ∂μ) ≤
      Real.log (∫ ω, Real.exp (t * ∑ i ∈ A, X i ω) ∂μ) +
        t * M * ((B.card - A.card : ℕ) : ℝ) := by
  have hE (S : Finset ℤ) : Integrable (fun ω => Real.exp (t * ∑ i ∈ S, X i ω)) μ :=
    integrable_exp_of_abs_le (μ := μ)
      (Finset.measurable_sum S (fun i _ => hX i)).aemeasurable
      (Filter.Eventually.of_forall (abs_sum_le_card_mul X S (fun i _ => hbound i))) t
  have hEA := hE A
  have hEB := hE B
  have hpoint (ω : Ω) : Real.exp (t * ∑ i ∈ B, X i ω) ≤
      Real.exp (t * M * ((B.card - A.card : ℕ) : ℝ)) *
        Real.exp (t * ∑ i ∈ A, X i ω) := by
    have hs : (∑ i ∈ B \ A, X i ω) + (∑ i ∈ A, X i ω) = ∑ i ∈ B, X i ω :=
      Finset.sum_sdiff hA
    have hb := abs_sum_le_card_mul X (B \ A) (fun i _ => hbound i) ω
    rw [Finset.card_sdiff_of_subset hA] at hb
    have hsum := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb) ht
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [← hs]
    nlinarith only [hsum]
  have hi := integral_mono hEB (hEA.const_mul
    (Real.exp (t * M * ((B.card - A.card : ℕ) : ℝ)))) hpoint
  rw [integral_const_mul] at hi
  have hl := Real.log_le_log (integral_exp_pos hEB) hi
  rw [Real.log_mul (Real.exp_pos _).ne' (integral_exp_pos hEA).ne', Real.log_exp] at hl
  linarith only [hl]

/-- Replacing an interval of length `n` by its depth-`N` rounded Cantor subset
costs at most `t*M*(N*delta*n + 2*(2^N-1))` in the upper log-Laplace bound.
The deletion fraction belongs to `[0,1]`; no centering or mixing is required. -/
theorem cantor_complete_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i)) {M δ t : ℝ}
    (hM : 0 ≤ M) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hbound : ∀ i ω, |X i ω| ≤ M) (ht : 0 ≤ t) (n N : ℕ) (a : ℤ) :
    Real.log (∫ ω, Real.exp (t * ∑ i ∈ Finset.Ico a (a + n), X i ω) ∂μ) ≤
      Real.log (∫ ω, Real.exp
        (t * ∑ i ∈ cantorBlock (cantorLength δ n) 0 a N, X i ω) ∂μ) +
          t * M * ((N : ℝ) * δ * n + 2 * ((2 : ℝ) ^ N - 1)) := by
  have hsub := cantorBlock_subset (cantorLength δ n) (cantorLength_fit δ n) 0 a N
  simp only [cantorLength] at hsub
  have h := removed_coordinates_laplace_le μ X hX hbound ht
    (cantorBlock (cantorLength δ n) 0 a N) (Finset.Ico a (a + n)) hsub
  have hcard := cantorBlock_card_le (cantorLength δ n) (cantorLength_fit δ n) 0 a N
  simp only [cantorLength] at hcard
  have hret := cantorLength_retained hδ0 hδ1 n N
  have hcardR : ((cantorBlock (cantorLength δ n) 0 a N).card : ℝ) =
      (2 : ℝ) ^ N * cantorLength δ n N := by
    rw [cantorBlock_card _ (cantorLength_fit δ n)]
    simp only [Nat.zero_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hrem : ((n - (cantorBlock (cantorLength δ n) 0 a N).card : ℕ) : ℝ) ≤
      (N : ℝ) * δ * n + 2 * ((2 : ℝ) ^ N - 1) := by
    rw [Nat.cast_sub hcard, hcardR]
    nlinarith only [hret]
  have hI : (Finset.Ico a (a + (n : ℤ))).card = n := by simp
  rw [hI] at h
  exact h.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hrem (mul_nonneg ht hM)))

end StrongMixing
