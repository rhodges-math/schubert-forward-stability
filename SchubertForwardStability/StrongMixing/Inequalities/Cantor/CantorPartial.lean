import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorLaplace

/-!
# Partial-depth decoupling of a fixed Cantor block

The total retained set is fixed by an outer depth and an inner depth. Splitting
only the outer levels leaves Cantor subsets inside the terminal intervals rather
than changing the retained set with the Laplace parameter.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Sum of log-Laplace transforms after splitting a fixed Cantor block through
`outer` levels, leaving Cantor blocks of depth `inner` at the terminal nodes.
The total retained block has depth `outer + inner`. -/
noncomputable def cantorPartialLog (μ : Measure Ω) (X : ℤ → Ω → ℝ) (L : ℕ → ℕ)
    (j : ℕ) (a : ℤ) (t : ℝ) (inner : ℕ) : ℕ → ℝ
  | 0 => Real.log (∫ ω, Real.exp (t * ∑ i ∈ cantorBlock L j a inner, X i ω) ∂μ)
  | d + 1 => cantorPartialLog μ X L (j + 1) a t inner d +
      cantorPartialLog μ X L (j + 1) (a + L j - L (j + 1)) t inner d

/-- A fixed Cantor block of total depth `outer + inner` can be decoupled through
only its outer levels. The error is the explicit dyadic mixing sum over those
levels, and the terminal terms retain their inner Cantor subsets. The hypotheses are
centering, uniform boundedness and the child-fit condition of the length schedule. -/
theorem cantor_partial_laplace_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i ω, |X i ω| ≤ M) (L : ℕ → ℕ)
    (hL : ∀ j, 2 * L (j + 1) ≤ L j) (j : ℕ) (a : ℤ) (t : ℝ)
    (outer inner : ℕ) :
    Real.log (∫ ω, Real.exp (t * ∑ i ∈ cantorBlock L j a (outer + inner), X i ω) ∂μ) ≤
      cantorPartialLog μ X L j a t inner outer +
        ∑ k ∈ Finset.range outer, (2 : ℝ) ^ k *
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
  change _ ≤ cantorPartialLog μ X L j a t inner outer +
    ∑ k ∈ Finset.range outer, (2 : ℝ) ^ k * e (j + k)
  induction outer generalizing j a with
  | zero =>
    simp only [Nat.zero_add, cantorPartialLog, Finset.sum_range_zero, add_zero]
    exact le_rfl
  | succ d ih =>
    let A := cantorBlock L (j + 1) a (d + inner)
    let B := cantorBlock L (j + 1) (a + L j - L (j + 1)) (d + inner)
    let cut := a + L (j + 1) - 1
    let gap := L j - 2 * L (j + 1) + 1
    let F := generatedSigma X {i | i ≤ cut}
    let G := generatedSigma X {i | cut + (gap : ℤ) ≤ i}
    let : MeasurableSpace Ω := mΩ
    have hs := cantorBlock_separated L hL j a (d + inner)
    have hA : @Measurable Ω ℝ F _ (fun ω => ∑ i ∈ A, X i ω) :=
      measurable_sum_generated X A _ hs.1
    have hB : @Measurable Ω ℝ G _ (fun ω => ∑ i ∈ B, X i ω) :=
      measurable_sum_generated X B _ hs.2
    have hbA : ∀ ω, |∑ i ∈ A, X i ω| ≤ (L (j + 1) : ℝ) * M := by
      intro ω
      apply (abs_sum_le_card_mul X A (fun i _ => hbound i) ω).trans
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast cantorBlock_card_le L hL (j + 1) a (d + inner)) hM
    have hbB : ∀ ω, |∑ i ∈ B, X i ω| ≤ (L (j + 1) : ℝ) * M := by
      intro ω
      apply (abs_sum_le_card_mul X B (fun i _ => hbound i) ω).trans
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast (cantorBlock_card_le L hL (j + 1)
          (a + L j - L (j + 1)) (d + inner))) hM
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
    have hroot : ∀ ω, (∑ i ∈ cantorBlock L j a ((d + 1) + inner), X i ω) =
        (∑ i ∈ A, X i ω) + ∑ i ∈ B, X i ω := by
      intro ω
      have hid : (d + 1) + inner = (d + inner) + 1 := by omega
      rw [hid, cantorBlock,
        Finset.sum_union (cantorBlock_disjoint L hL j a (d + inner))]
    simp_rw [hroot]
    refine (hp.trans (add_le_add le_rfl he)).trans ?_
    have hiA := ih (j + 1) a
    have hiB := ih (j + 1) (a + L j - L (j + 1))
    calc
      _ ≤ (cantorPartialLog μ X L (j + 1) a t inner d +
          ∑ k ∈ Finset.range d, (2 : ℝ) ^ k * e (j + 1 + k)) +
          (cantorPartialLog μ X L (j + 1) (a + L j - L (j + 1)) t inner d +
          ∑ k ∈ Finset.range d, (2 : ℝ) ^ k * e (j + 1 + k)) + e j :=
        add_le_add (add_le_add hiA hiB) le_rfl
      _ = cantorPartialLog μ X L j a t inner (d + 1) +
          ∑ k ∈ Finset.range (d + 1), (2 : ℝ) ^ k * e (j + k) := by
        rw [cantorPartialLog, sum_dyadic_shift]
        ring

end StrongMixing
