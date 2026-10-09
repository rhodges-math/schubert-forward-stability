import SchubertForwardStability.StrongMixing.Inequalities.SubsetRemainder
import SchubertForwardStability.StrongMixing.Inequalities.Cantor.CantorQuadratic

/-!
# Retained Cantor subsets after coordinate compression

The retained coordinate set is transported through the sorted integer extension.
Its definition is independent of the Laplace parameter. The module gives subset
inclusion, the cardinality bound, the transport of finite sums and the quadratic
Laplace estimate.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

/-- The retained Cantor subset of a nonempty finite integer coordinate set is the
image of its rounded length schedule under its sorted integer extension.
Deletion fraction and depth are fixed arguments, independent of `t`. -/
noncomputable def compressedCantorSet (A : Finset ℤ) (hA : A.Nonempty) (δ : ℝ) (N : ℕ) :
    Finset ℤ :=
  (cantorBlock (cantorLength δ A.card) 0 0 N).image (finiteSetExtension A hA)

/-- The compressed Cantor set is contained in its original nonempty
finite coordinate set, for every real deletion fraction and natural depth. -/
theorem compressedCantorSet_subset (A : Finset ℤ) (hA : A.Nonempty) (δ : ℝ) (N : ℕ) :
    compressedCantorSet A hA δ N ⊆ A := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  apply finiteSetExtension_mem A hA
  have h := cantorBlock_subset (cantorLength δ A.card)
    (cantorLength_fit δ A.card) 0 0 N hj
  simpa only [cantorLength, zero_add] using h

/-- Sorted integer compression preserves the cardinality of the retained Cantor
set because its reindexing is strictly increasing and hence injective. -/
theorem compressedCantorSet_card (A : Finset ℤ) (hA : A.Nonempty) (δ : ℝ) (N : ℕ) :
    (compressedCantorSet A hA δ N).card = (cantorBlock (cantorLength δ A.card) 0 0 N).card := by
  exact Finset.card_image_of_injective _ (finiteSetExtension_strictMono A hA).injective

/-- Every real coordinate sum over a retained Cantor set after sorted compression
is exactly the coordinate sum over its image in the original row. -/
theorem compressedCantorSet_sum (A : Finset ℤ) (hA : A.Nonempty) (δ : ℝ) (N : ℕ)
    (f : ℤ → ℝ) :
    (∑ i ∈ cantorBlock (cantorLength δ A.card) 0 0 N, f (finiteSetExtension A hA i)) =
      ∑ i ∈ compressedCantorSet A hA δ N, f i := by
  symm
  rw [compressedCantorSet, Finset.sum_image]
  intro i _hi j _hj hij
  exact (finiteSetExtension_strictMono A hA).injective hij

/-- A compressed Cantor subset retains at least half of the original coordinates
when `N*delta<=1/4`, `2^N<=card(A)/8`, and `delta` belongs to `[0,1]`.
The bound does not involve the Laplace parameter `t`. -/
theorem compressedCantorSet_half (A : Finset ℤ) (hA : A.Nonempty) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (N : ℕ)
    (hfrac : (N : ℝ) * δ ≤ 1 / 4) (hround : (2 : ℝ) ^ N ≤ (A.card : ℝ) / 8) :
    (A.card : ℝ) / 2 ≤ (compressedCantorSet A hA δ N).card := by
  rw [compressedCantorSet_card]
  exact cantorBlock_half hδ0 hδ1 A.card N 0 hfrac hround

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The compressed retained Cantor set satisfies the pure quadratic
log-Laplace bound `card(A)*(t*M)^2*(6*K_c+384/c^2)`. The centered bounded
geometric-mixing hypotheses and the terminal size, multiplicity and
separation conditions transfer through the increasing reindexing. -/
theorem compressed_cantor_quadratic_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℤ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {M c δ t : ℝ}
    (hM : 0 < M) (hc : 0 < c) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hbound : ∀ i ω, |X i ω| ≤ M)
    (hmix : ∀ h : ℕ, 1 ≤ h → mixingCoeff μ X h ≤ Real.exp (-2 * c * h))
    (A : Finset ℤ) (hA : A.Nonempty) (N : ℕ) (ht : 0 < t) (hsmall : t * M ≤ 1 / 8)
    (hfinal : (t * M) ^ 2 * cantorLength δ A.card N ≤ c / 24)
    (hpow : (2 : ℝ) ^ N ≤ A.card) (hsep : t * M ≤ c * δ / 3) :
    Real.log (∫ ω, Real.exp (t * ∑ i ∈ compressedCantorSet A hA δ N, X i ω) ∂μ) ≤
      A.card * (t * M) ^ 2 *
        (6 * (1 + 8 * Real.exp (-2 * c) / (1 - Real.exp (-2 * c))) + 384 / c ^ 2) := by
  have h := cantor_stopped_quadratic_le μ (fun i => X (finiteSetExtension A hA i))
    (fun i => hX _) (fun i => hcenter _) hM hc hδ0 hδ1 (fun i ω => hbound _ ω)
    (fun h hh => (mixingCoeff_finiteSet_le μ X A hA h).trans (hmix h hh))
    A.card N 0 ht hsmall hfinal hpow hsep
  have hs (ω : Ω) : (∑ i ∈ cantorBlock (cantorLength δ A.card) 0 0 N,
      X (finiteSetExtension A hA i) ω) = ∑ i ∈ compressedCantorSet A hA δ N, X i ω :=
    compressedCantorSet_sum A hA δ N (fun i => X i ω)
  simpa only [hs] using h

end StrongMixing
