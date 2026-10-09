import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorBlocks
import SchubertForwardStability.StrongMixing.Inequalities.Laplace.LaplaceLogs
import SchubertForwardStability.StrongMixing.Inequalities.Laplace.SeparatedLaplace

/-!
# Log-Laplace decoupling for finite Cantor blocks

The explicit integer Cantor construction is combined with the centered
two-block mixing inequality. The resulting error is the exact dyadic sum over
deleted gaps, while terminal transforms remain explicit until moment bounds apply.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

/-- The dyadic error series through level `d + 1` consists of its initial error
and twice the corresponding depth-`d` series starting one level later. -/
theorem sum_dyadic_shift (e : ℕ → ℝ) (j d : ℕ) :
    (∑ k ∈ Finset.range (d + 1), (2 : ℝ) ^ k * e (j + k)) =
      e j + 2 * ∑ k ∈ Finset.range d, (2 : ℝ) ^ k * e (j + 1 + k) := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.add_zero, one_mul]
  have hs : (∑ k ∈ Finset.range d, (2 : ℝ) ^ (k + 1) * e (j + (k + 1))) =
      2 * ∑ k ∈ Finset.range d, (2 : ℝ) ^ k * e (j + 1 + k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hj : j + (k + 1) = j + 1 + k := by omega
    rw [hj, pow_succ]
    ring
  rw [hs, add_comm]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Sum of terminal log-Laplace transforms in the recursively retained integer
Cantor block. Each terminal half-open interval contributes its own coordinate sum.
The recursion follows the same two translated child intervals as `cantorBlock`. -/
noncomputable def cantorLeafLog (μ : Measure Ω) (X : ℤ → Ω → ℝ) (L : ℕ → ℕ)
    (j : ℕ) (a : ℤ) (t : ℝ) : ℕ → ℝ
  | 0 => Real.log (∫ ω, Real.exp (t * ∑ i ∈ Finset.Ico a (a + L j), X i ω) ∂μ)
  | d + 1 => cantorLeafLog μ X L (j + 1) a t d +
      cantorLeafLog μ X L (j + 1) (a + L j - L (j + 1)) t d

/-- A finite integer Cantor block of centered uniformly bounded coordinates has
log-Laplace transform at most its terminal-transform sum and an explicit dyadic
mixing-error series. The gap at level `q` is `L q - 2 * L (q + 1) + 1`. The length
schedule is arbitrary, subject only to the child-fit condition of the construction. -/
theorem cantor_log_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ω, |X i ω| ≤ M) (L : ℕ → ℕ)
    (hL : ∀ j, 2 * L (j + 1) ≤ L j) (j : ℕ) (a : ℤ) (t : ℝ) (d : ℕ) :
    Real.log (∫ ω, Real.exp (t * ∑ i ∈ cantorBlock L j a d, X i ω) ∂μ) ≤
      cantorLeafLog μ X L j a t d +
        ∑ k ∈ Finset.range d, (2 : ℝ) ^ k *
          (Real.exp (2 * |t| * M * L (j + k + 1)) *
            mixingCoeff μ X (L (j + k) - 2 * L (j + k + 1) + 1)) := by
  have hI : ∀ i, Integrable (X i) μ := fun i =>
    (MemLp.of_bound (p := 1) (hX i).aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun ω => by simpa using hbound i ω))).integrable le_rfl
  have hC : ∀ A : Finset ℤ, (∫ ω, ∑ i ∈ A, X i ω ∂μ) = 0 := by
    intro A
    rw [integral_finsetSum _ (fun i _ => hI i)]
    simp [hcenter]
  let e : ℕ → ℝ := fun q => Real.exp (2 * |t| * M * L (q + 1)) *
    mixingCoeff μ X (L q - 2 * L (q + 1) + 1)
  change _ ≤ cantorLeafLog μ X L j a t d +
    ∑ k ∈ Finset.range d, (2 : ℝ) ^ k * e (j + k)
  induction d generalizing j a with
  | zero => simp [cantorBlock, cantorLeafLog]
  | succ d ih =>
    let A := cantorBlock L (j + 1) a d
    let B := cantorBlock L (j + 1) (a + L j - L (j + 1)) d
    let cut := a + L (j + 1) - 1
    let gap := L j - 2 * L (j + 1) + 1
    let F := generatedSigma X {i | i ≤ cut}
    let G := generatedSigma X {i | cut + (gap : ℤ) ≤ i}
    let : MeasurableSpace Ω := mΩ
    have hs := cantorBlock_separated L hL j a d
    have hA : @Measurable Ω ℝ F _ (fun ω => ∑ i ∈ A, X i ω) :=
      measurable_sum_generated X A _ hs.1
    have hB : @Measurable Ω ℝ G _ (fun ω => ∑ i ∈ B, X i ω) :=
      measurable_sum_generated X B _ hs.2
    have hbA : ∀ ω, |∑ i ∈ A, X i ω| ≤ (L (j + 1) : ℝ) * M := by
      intro ω
      apply (abs_sum_le_card_mul X A (fun i _ => hbound i) ω).trans
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast cantorBlock_card_le L hL (j + 1) a d) hM
    have hbB : ∀ ω, |∑ i ∈ B, X i ω| ≤ (L (j + 1) : ℝ) * M := by
      intro ω
      apply (abs_sum_le_card_mul X B (fun i _ => hbound i) ω).trans
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast (cantorBlock_card_le L hL (j + 1)
          (a + L j - L (j + 1)) d)) hM
    have hp := log_laplace_product_error_le μ F G
      (generatedSigma_le X _ (fun i _ => hX i))
      (generatedSigma_le X _ (fun i _ => hX i))
      (fun ω => ∑ i ∈ A, X i ω) (fun ω => ∑ i ∈ B, X i ω)
      hA hB hbA hbB (hC A) (hC B) t
    have he : Real.exp (|t| * ((L (j + 1) : ℝ) * M + L (j + 1) * M)) *
        strongMixingCoeff (mΩ := mΩ) μ F G ≤ e j := by
      have hid : |t| * ((L (j + 1) : ℝ) * M + L (j + 1) * M) =
          2 * |t| * M * L (j + 1) := by ring
      rw [hid]
      exact mul_le_mul_of_nonneg_left (cutCoeff_le_mixingCoeff μ X gap cut)
        (Real.exp_nonneg _)
    have hroot : ∀ ω, (∑ i ∈ cantorBlock L j a (d + 1), X i ω) =
        (∑ i ∈ A, X i ω) + ∑ i ∈ B, X i ω := by
      intro ω
      rw [cantorBlock, Finset.sum_union (cantorBlock_disjoint L hL j a d)]
    simp_rw [hroot]
    refine (hp.trans (add_le_add le_rfl he)).trans ?_
    have hiA := ih (j + 1) a
    have hiB := ih (j + 1) (a + L j - L (j + 1))
    calc
      _ ≤ (cantorLeafLog μ X L (j + 1) a t d +
          ∑ k ∈ Finset.range d, (2 : ℝ) ^ k * e (j + 1 + k)) +
          (cantorLeafLog μ X L (j + 1) (a + L j - L (j + 1)) t d +
          ∑ k ∈ Finset.range d, (2 : ℝ) ^ k * e (j + 1 + k)) + e j :=
        add_le_add (add_le_add hiA hiB) le_rfl
      _ = cantorLeafLog μ X L j a t (d + 1) +
          ∑ k ∈ Finset.range (d + 1), (2 : ℝ) ^ k * e (j + k) := by
        rw [cantorLeafLog, sum_dyadic_shift]
        ring

end StrongMixing
