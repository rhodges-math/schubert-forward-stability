import SchubertForwardStability.StrongMixing.Inequalities.Laplace.FiniteDyadic
import SchubertForwardStability.StrongMixing.Inequalities.Laplace.SeparatedLaplace

/-!
# Finite-depth decoupling of integer coordinate blocks

Finite block partitions require only the split and separation hypotheses
above their terminal depth. Their log-Laplace error is bounded by the sequence's
defined mixing coefficient, with every internal-node exponential factor explicit.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Through a specified finite depth, a binary partition of finite centered bounded
integer-coordinate blocks satisfies the terminal-transform plus mixing-error estimate.
Splits, disjointness and separation are required only above the terminal depth.
The terminal blocks may be empty, and every natural separation lag is allowed. -/
theorem finite_block_log_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (depth : ℕ) (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M : ℝ}
    (hbound : ∀ i ω, |X i ω| ≤ M) (B : ℕ → ℕ → Finset ℤ)
    (hsplit : ∀ j i, j < depth →
      B j i = B (j + 1) (2 * i) ∪ B (j + 1) (2 * i + 1))
    (hdisj : ∀ j i, j < depth →
      Disjoint (B (j + 1) (2 * i)) (B (j + 1) (2 * i + 1)))
    (cut : ℕ → ℕ → ℤ) (gap : ℕ → ℕ → ℕ)
    (hleft : ∀ j i, j < depth → ∀ a, a ∈ B (j + 1) (2 * i) → a ≤ cut j i)
    (hright : ∀ j i, j < depth → ∀ b,
      b ∈ B (j + 1) (2 * i + 1) → cut j i + gap j i ≤ b) (t : ℝ) :
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
  have hZcenter : ∀ j i, j ≤ depth → ∫ ω, Z j i ω ∂μ = 0 := by
    intro j i _
    dsimp [Z]
    rw [integral_finsetSum _ (fun a _ => hI a)]
    simp [hcenter]
  have hZsplit : ∀ j i, j < depth → ∀ ω,
      Z j i ω = Z (j + 1) (2 * i) ω + Z (j + 1) (2 * i + 1) ω := by
    intro j i hj ω
    dsimp [Z]
    rw [hsplit j i hj, Finset.sum_union (hdisj j i hj)]
  have hd := finite_dyadic_log_laplace_le μ depth Z F G
    (fun j i _ => generatedSigma_le X _ (fun a _ => hX a))
    (fun j i _ => generatedSigma_le X _ (fun a _ => hX a))
    (fun j i hj => measurable_sum_generated X _ _ (hleft j i hj))
    (fun j i hj => measurable_sum_generated X _ _ (hright j i hj))
    (fun j i => ((B (j + 1) (2 * i)).card : ℝ) * M)
    (fun j i => ((B (j + 1) (2 * i + 1)).card : ℝ) * M)
    (fun j i _ ω => abs_sum_le_card_mul X _ (fun a _ => hbound a) ω)
    (fun j i _ ω => abs_sum_le_card_mul X _ (fun a _ => hbound a) ω)
    hZcenter hZsplit t
  refine hd.trans (add_le_add le_rfl (Finset.sum_le_sum (fun j _ =>
    Finset.sum_le_sum (fun i _ => ?_))))
  have heq : ((B (j + 1) (2 * i)).card : ℝ) * M +
      ((B (j + 1) (2 * i + 1)).card : ℝ) * M =
        M * ((B (j + 1) (2 * i)).card + (B (j + 1) (2 * i + 1)).card) := by ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (cutCoeff_le_mixingCoeff μ X (gap j i) (cut j i))
    (Real.exp_nonneg _)

end StrongMixing
