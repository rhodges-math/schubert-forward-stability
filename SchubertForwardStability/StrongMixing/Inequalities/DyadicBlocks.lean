import SchubertForwardStability.StrongMixing.Inequalities.Laplace.DyadicLaplace
import SchubertForwardStability.StrongMixing.Inequalities.Laplace.SeparatedLaplace

/-!
# Dyadic decoupling for finite coordinate blocks

The dyadic logarithmic estimate is specialized to sums over finite sets of integer
coordinates. Child sets are disjoint and partition their parent, and their
separation determines the mixing coefficient of the sequence used at each node.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- For a binary partition of finite integer-coordinate blocks of centered
uniformly bounded variables, the root log-Laplace transform is at most the sum of
the terminal transforms and the explicit mixing error at every internal node.
Empty blocks and zero gaps are allowed; separation and disjointness are hypotheses on
the coordinate sets. -/
theorem dyadic_block_log_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M : ℝ}
    (hbound : ∀ i ω, |X i ω| ≤ M) (B : ℕ → ℕ → Finset ℤ)
    (hsplit : ∀ j i, B j i = B (j + 1) (2 * i) ∪ B (j + 1) (2 * i + 1))
    (hdisj : ∀ j i, Disjoint (B (j + 1) (2 * i)) (B (j + 1) (2 * i + 1)))
    (cut : ℕ → ℕ → ℤ) (gap : ℕ → ℕ → ℕ)
    (hleft : ∀ j i a, a ∈ B (j + 1) (2 * i) → a ≤ cut j i)
    (hright : ∀ j i b, b ∈ B (j + 1) (2 * i + 1) → cut j i + gap j i ≤ b)
    (t : ℝ) (depth : ℕ) :
    Real.log (∫ ω, Real.exp (t * ∑ a ∈ B 0 0, X a ω) ∂μ) ≤
      (∑ i ∈ Finset.range (2 ^ depth),
        Real.log (∫ ω, Real.exp (t * ∑ a ∈ B depth i, X a ω) ∂μ)) +
      ∑ j ∈ Finset.range depth, ∑ i ∈ Finset.range (2 ^ j),
        Real.exp (|t| * (M * ((B (j + 1) (2 * i)).card +
          (B (j + 1) (2 * i + 1)).card))) * mixingCoeff μ X (gap j i) := by
  let Z : ℕ → ℕ → Ω → ℝ := fun j i ω => ∑ a ∈ B j i, X a ω
  let F : ℕ → ℕ → MeasurableSpace Ω := fun j i =>
    generatedSigma X {a | a ≤ cut j i}
  let G : ℕ → ℕ → MeasurableSpace Ω := fun j i =>
    generatedSigma X {a | cut j i + gap j i ≤ a}
  have hI : ∀ a, Integrable (X a) μ := fun a =>
    (MemLp.of_bound (p := 1) (hX a).aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun ω => by simpa using hbound a ω))).integrable le_rfl
  have hZcenter : ∀ j i, ∫ ω, Z j i ω ∂μ = 0 := by
    intro j i
    dsimp [Z]
    rw [integral_finsetSum _ (fun a _ => hI a)]
    simp [hcenter]
  have hZsplit : ∀ j i ω, Z j i ω = Z (j + 1) (2 * i) ω +
      Z (j + 1) (2 * i + 1) ω := by
    intro j i ω
    dsimp [Z]
    rw [hsplit, Finset.sum_union (hdisj j i)]
  have hd := dyadic_log_laplace_le μ Z F G
    (fun j i => generatedSigma_le X _ (fun a _ => hX a))
    (fun j i => generatedSigma_le X _ (fun a _ => hX a))
    (fun j i => measurable_sum_generated X _ _ (hleft j i))
    (fun j i => measurable_sum_generated X _ _ (hright j i))
    (fun j i => ((B (j + 1) (2 * i)).card : ℝ) * M)
    (fun j i => ((B (j + 1) (2 * i + 1)).card : ℝ) * M)
    (fun j i ω => abs_sum_le_card_mul X _ (fun a _ => hbound a) ω)
    (fun j i ω => abs_sum_le_card_mul X _ (fun a _ => hbound a) ω)
    hZcenter hZsplit t depth
  refine hd.trans (add_le_add le_rfl (Finset.sum_le_sum (fun j _ =>
    Finset.sum_le_sum (fun i _ => ?_))))
  have heq : ((B (j + 1) (2 * i)).card : ℝ) * M +
      ((B (j + 1) (2 * i + 1)).card : ℝ) * M =
        M * ((B (j + 1) (2 * i)).card + (B (j + 1) (2 * i + 1)).card) := by ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (cutCoeff_le_mixingCoeff μ X (gap j i) (cut j i))
    (Real.exp_nonneg _)

end StrongMixing
