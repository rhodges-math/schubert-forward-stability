import SchubertForwardStability.StrongMixing.Inequalities.BlockProducts
import SchubertForwardStability.StrongMixing.Inequalities.SubsetIntervals
import SchubertForwardStability.StrongMixing.Inequalities.Laplace.SeparatedLaplace

/-!
# Finite separated coordinate blocks

Geometric separation of finite coordinate blocks places their generated fields
inside a past/future cut of the original sequence. The block-product bound thus
has an error controlled by the lag coefficient of the sequence.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Finite blocks of a centered, bounded real sequence have log-Laplace transform
at most the sum of block transforms plus the Ibragimov error using `alpha(gap)`.
The hypotheses are that every prefix and the remaining suffix lie on either side of
an integer cut with the stated natural gap.
The finite block family may be empty, and blocks themselves may be empty. -/
theorem separated_block_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M : ℝ}
    (hbound : ∀ i ω, |X i ω| ≤ M) (A : ℕ → Finset ℤ) (p gap : ℕ)
    (hsep : ∀ k : ℕ, 1 ≤ k → k < p → ∃ cut : ℤ,
      (∀ i : ℕ, i < k → ∀ j ∈ A i, j ≤ cut) ∧
      (∀ i : ℕ, k ≤ i → i < p → ∀ j ∈ A i, cut + (gap : ℤ) ≤ j)) (t : ℝ) :
    Real.log (∫ ω, Real.exp (t * ∑ i ∈ Finset.range p, ∑ j ∈ A i, X j ω) ∂μ) ≤
      (∑ i ∈ Finset.range p, Real.log (∫ ω, Real.exp (t * ∑ j ∈ A i, X j ω) ∂μ)) +
        ((p - 1 : ℕ) : ℝ) * mixingCoeff μ X gap *
          Real.exp (|t| * ∑ i ∈ Finset.range p, (A i).card * M) := by
  let Z : ℕ → Ω → ℝ := fun i ω => ∑ j ∈ A i, X j ω
  have hz : ∀ i, Measurable (Z i) := fun i =>
    Finset.measurable_sum (A i) (fun j _ => hX j)
  have hi : ∀ j, Integrable (X j) μ := fun j =>
    (MemLp.of_bound (p := 1) (hX j).aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun ω => by simpa using hbound j ω))).integrable le_rfl
  have hc : ∀ i, ∫ ω, Z i ω ∂μ = 0 := by
    intro i
    rw [integral_finsetSum (A i) (f := X) (fun j _ => hi j)]
    simp only [hcenter, Finset.sum_const_zero]
  apply block_product_laplace_le μ Z hz (fun i => (A i).card * M)
    (fun i => abs_sum_le_card_mul X (A i) (fun j _ => hbound j)) hc
    (mixingCoeff_nonneg μ X gap) p _ t
  intro k hk hkp
  obtain ⟨cut, hp, hf⟩ := hsep k hk hkp
  have hpS : generatedSigma Z {i | i < k} ≤ generatedSigma X {j | j ≤ cut} := by
    let : MeasurableSpace Ω := generatedSigma X {j | j ≤ cut}
    apply generatedSigma_le
    intro i hi
    exact measurable_sum_generated X (A i) _ (hp i hi)
  have hfS : generatedSigma Z {i | k ≤ i ∧ i < p} ≤
      generatedSigma X {j | cut + (gap : ℤ) ≤ j} := by
    let : MeasurableSpace Ω := generatedSigma X {j | cut + (gap : ℤ) ≤ j}
    apply generatedSigma_le
    intro i hi
    exact measurable_sum_generated X (A i) _ (hf i hi.1 hi.2)
  exact (strongMixingCoeff_mono μ hpS hfS).trans
    (cutCoeff_le_mixingCoeff μ X gap cut)

/-- If every separated block is a subset of an interval of length `len`, each
short block has the quadratic transform bound. Combining them gives the
explicit geometric decoupling error at lag `gap`. The small-parameter condition is
`|t|*len*M <= 1`. -/
theorem separated_short_blocks_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : ℕ → Finset ℤ) (p gap len : ℕ) (hgap : 1 ≤ gap) (a : ℕ → ℤ)
    (hA : ∀ i, A i ⊆ Finset.Ico (a i) (a i + len))
    (hsep : ∀ k : ℕ, 1 ≤ k → k < p → ∃ cut : ℤ,
      (∀ i : ℕ, i < k → ∀ j ∈ A i, j ≤ cut) ∧
      (∀ i : ℕ, k ≤ i → i < p → ∀ j ∈ A i, cut + (gap : ℤ) ≤ j))
    (t : ℝ) (hsmall : |t| * len * M ≤ 1) :
    Real.log (∫ ω, Real.exp (t * ∑ i ∈ Finset.range p, ∑ j ∈ A i, X j ω) ∂μ) ≤
      p * t ^ 2 * len * M ^ 2 *
          (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) +
        ((p - 1 : ℕ) : ℝ) *
          Real.exp (-2 * c * gap + |t| * ∑ i ∈ Finset.range p, (A i).card * M) := by
  have hr1 : Real.exp (-2 * c) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hmixR : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c) ^ h := by
    intro h hh
    simpa only [← Real.exp_nat_mul, mul_comm (h : ℝ)] using hmix h hh
  have hbase := separated_block_laplace_le μ X hX hcenter hbound A p gap hsep t
  refine hbase.trans (add_le_add ?_ ?_)
  · calc
      _ ≤ ∑ _i ∈ Finset.range p, t ^ 2 * len * M ^ 2 *
          (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) :=
        Finset.sum_le_sum (fun i _ => subset_interval_laplace_le μ X hX hcenter hM
          hbound (Real.exp_pos _).le hr1 hmixR (A i) (a i) len (hA i) t hsmall)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  · calc
      _ ≤ ((p - 1 : ℕ) : ℝ) * Real.exp (-2 * c * gap) *
          Real.exp (|t| * ∑ i ∈ Finset.range p, (A i).card * M) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hmix gap hgap) (Nat.cast_nonneg _))
            (Real.exp_nonneg _)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]

end StrongMixing
