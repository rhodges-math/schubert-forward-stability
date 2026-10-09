import SchubertForwardStability.StrongMixing.Inequalities.AlternatingBlocks
import SchubertForwardStability.StrongMixing.Inequalities.Laplace.LaplaceCombination
import Mathlib.Data.Fintype.BigOperators

/-!
# Alternating short-block log-Laplace estimates

The even and odd chunk families are separately decoupled using their
integer gaps. Weighted Jensen combines the two family transforms, which need not be
independent. All finite block errors are explicit.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Two bounded measurable real variables have log-Laplace transform of their
sum at most the average of their transforms at twice the parameter. This is the
two-weight Jensen inequality and requires no independence or centering. -/
theorem log_laplace_add_half_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) {M N : ℝ}
    (hb : ∀ ω, |f ω| ≤ M) (hc : ∀ ω, |g ω| ≤ N) (t : ℝ) :
    Real.log (∫ ω, Real.exp (t * (f ω + g ω)) ∂μ) ≤
      (1 / 2) * Real.log (∫ ω, Real.exp ((2 * t) * f ω) ∂μ) +
        (1 / 2) * Real.log (∫ ω, Real.exp ((2 * t) * g ω) ∂μ) := by
  let Z : Bool → Ω → ℝ := fun b => if b then g else f
  have hz : ∀ b ∈ (Finset.univ : Finset Bool), AEMeasurable (Z b) μ := by
    intro b _hb
    cases b
    · exact hf.aemeasurable
    · exact hg.aemeasurable
  have hi : ∀ b ∈ (Finset.univ : Finset Bool),
      Integrable (fun ω => Real.exp (t * Z b ω / (1 / 2))) μ := by
    intro b _hb
    have heq : (fun ω => Real.exp (t * Z b ω / (1 / 2))) =
        (fun ω => Real.exp ((2 * t) * Z b ω)) := by
      funext ω
      congr 1
      ring
    rw [heq]
    cases b
    · exact integrable_exp_of_abs_le (μ := μ) hf.aemeasurable
        (Filter.Eventually.of_forall hb) (2 * t)
    · exact integrable_exp_of_abs_le (μ := μ) hg.aemeasurable
        (Filter.Eventually.of_forall hc) (2 * t)
  have h := (log_laplace_weighted_le μ Finset.univ Z hz (fun _ => (1 / 2 : ℝ))
    (by norm_num) (by simp) t hi).2
  have heq : ∀ b ω, t * Z b ω / (1 / 2) = (2 * t) * Z b ω := by
    intro b ω
    ring
  simp_rw [heq] at h
  simpa [Z, Fintype.sum_bool, add_comm] using h

/-- An arbitrary finite set covered by `2*p` intervals of length `len` has a
quadratic log-Laplace bound plus one explicit geometric error. The hypotheses are
the lag bound and `2*|t|*len*M <= 1`; the sequence need not be stationary. -/
theorem alternating_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : Finset ℤ) (a : ℤ) (len p : ℕ) (hlen : 1 ≤ len)
    (hA : A ⊆ Finset.Ico a (a + (2 * p * len : ℕ)))
    (t : ℝ) (hsmall : 2 * |t| * len * M ≤ 1) :
    Real.log (∫ ω, Real.exp (t * ∑ j ∈ A, X j ω) ∂μ) ≤
      4 * p * t ^ 2 * len * M ^ 2 *
          (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) +
        ((p - 1 : ℕ) : ℝ) * Real.exp (-2 * c * len + 2 * |t| * p * len * M) := by
  let Z (parity : ℕ) (ω : Ω) :=
    ∑ i ∈ Finset.range p, ∑ j ∈ intervalChunk A a len (2 * i + parity), X j ω
  have hz : ∀ parity, Measurable (Z parity) := fun parity =>
    Finset.measurable_sum (Finset.range p) (fun i _ =>
      Finset.measurable_sum _ (fun j _ => hX j))
  have hcard (parity : ℕ) :
      (∑ i ∈ Finset.range p, (intervalChunk A a len (2 * i + parity)).card * M) ≤
        p * len * M := by
    calc
      _ ≤ ∑ _i ∈ Finset.range p, (len : ℝ) * M :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
          (by exact_mod_cast intervalChunk_card_le A a len (2 * i + parity)) hM)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hb (parity : ℕ) (ω : Ω) : |Z parity ω| ≤ p * len * M := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun i _ => abs_sum_le_card_mul X _
        (fun j _ => hbound j) ω)).trans (hcard parity))
  have hs : |2 * t| * len * M ≤ 1 := by
    simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hsmall
  let Q : ℝ := 4 * p * t ^ 2 * len * M ^ 2 *
    (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c)))
  let E : ℝ := ((p - 1 : ℕ) : ℝ) *
    Real.exp (-2 * c * len + 2 * |t| * p * len * M)
  have hpar (parity : ℕ) : Real.log (∫ ω, Real.exp ((2 * t) * Z parity ω) ∂μ) ≤ Q + E := by
    have h := separated_short_blocks_le μ X hX hcenter hM hc hbound hmix
      (fun i => intervalChunk A a len (2 * i + parity)) p len len hlen
      (fun i => a + ((2 * i + parity) * len : ℕ))
      (fun i => intervalChunk_subset A a len (2 * i + parity))
      (alternating_chunks_separated A a len parity p) (2 * t) hs
    refine h.trans (add_le_add (by dsimp [Q]; ring_nf; exact le_rfl) ?_)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (p - 1))
    apply Real.exp_le_exp.mpr
    have hboundCard := mul_le_mul_of_nonneg_left (hcard parity) (abs_nonneg (2 * t))
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hboundCard
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith only [hboundCard]
  have h := log_laplace_add_half_le μ (Z 0) (Z 1) (hz 0) (hz 1) (hb 0) (hb 1) t
  have hsum (ω : Ω) : (∑ j ∈ A, X j ω) = Z 0 ω + Z 1 ω := by
    simpa only [Z, Nat.add_zero] using alternating_chunks_sum A a len p (fun j => X j ω) hA
  simp_rw [hsum]
  refine h.trans ?_
  have h0 := mul_le_mul_of_nonneg_left (hpar 0) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h1 := mul_le_mul_of_nonneg_left (hpar 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  dsimp [Q, E] at h0 h1
  linarith only [h0, h1]

end StrongMixing
