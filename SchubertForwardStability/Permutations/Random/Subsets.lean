import SchubertForwardStability.Permutations.Random.Uniform
import SchubertForwardStability.Permutations.Classes.Grassmannian

/-! # Uniform subset encodings of Grassmannian permutations

## Main definitions

* `subsetLaw`: uniform sampling from all subsets of the initial positive interval.
* `subsetPermutation`: the ordered-subset permutation associated with a sampled subset.
* `grassmannianLaw`: the pushforward of uniform subset sampling.

## Implementation notes

The subset carrier has Mathlib's measurable structure on finsets, which is discrete. The encoding
map is total, with identity as its value outside the sampling family.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace FinitaryPerm

/-- Finite subsets of positive positions carry Mathlib's measurable structure on finsets, which
is discrete because the positive integers are countable. -/
example : DiscreteMeasurableSpace (Finset ℕ+) := inferInstance

/-- Uniform sampling from the subsets of the initial positive interval. -/
noncomputable def subsetLaw (n : ℕ) : Measure (Finset ℕ+) :=
  uniformOn ((positions n).powerset : Set (Finset ℕ+))

/-- Uniform subset sampling is a probability measure, including at size zero. -/
instance instIsProbabilityMeasureSubsetLaw (n : ℕ) : IsProbabilityMeasure (subsetLaw n) :=
  isProbabilityMeasure_uniformOn (positions n).powerset.finite_toSet
    ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩

/-- The total ordered-subset encoding, equal to identity outside the initial interval. -/
noncomputable def subsetPermutation (n : ℕ) (V : Finset ℕ+) : FinitaryPerm ℕ+ :=
  if h : V ⊆ positions n then grassmannianOfSubset n V h else 1

/-- On the sampling family the total encoding agrees with the ordered-subset constructor. -/
theorem subsetPermutation_eq (n : ℕ) (V : Finset ℕ+) (h : V ⊆ positions n) :
    subsetPermutation n V = grassmannianOfSubset n V h := by
  simp only [subsetPermutation, dite_eq_left h]

/-- The total subset encoding is measurable. -/
theorem measurable_subsetPermutation (n : ℕ) : Measurable (subsetPermutation n) :=
  measurable_of_countable _

/-- The subset-encoded Grassmannian law. -/
noncomputable def grassmannianLaw (n : ℕ) : Measure (FinitaryPerm ℕ+) :=
  (subsetLaw n).map (subsetPermutation n)

/-- The encoded Grassmannian law is a probability measure. -/
instance instIsProbabilityMeasureGrassLaw (n : ℕ) : IsProbabilityMeasure (grassmannianLaw n) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_subsetPermutation n).aemeasurable).mpr
    inferInstance

/-- The expectation of a real statistic of the encoding is its finite subset average. -/
theorem integral_subsetEncoding (n : ℕ) (X : FinitaryPerm ℕ+ → ℝ) :
    ∫ V, X (subsetPermutation n V) ∂subsetLaw n =
      ((2 : ℝ) ^ n)⁻¹ * ∑ V ∈ (positions n).powerset, X (subsetPermutation n V) := by
  rw [subsetLaw, integral_uniform_finset, Finset.card_powerset, card_positions, Nat.cast_pow]
  rfl

/-- Each admissible subset has point probability equal to the reciprocal of `2^n`. -/
theorem subsetLaw_singleton (n : ℕ) (V : Finset ℕ+) :
    subsetLaw n {V} = if V ⊆ positions n then ((2 : ℝ≥0∞) ^ n)⁻¹ else 0 := by
  rw [subsetLaw, uniformOn_finset_singleton]
  simp only [Finset.mem_powerset, Finset.card_powerset, card_positions,
    Nat.cast_pow, Nat.cast_ofNat]

/-- Expectations under the encoded law are finite averages over the subset encodings. -/
theorem integral_grassmannianLaw (n : ℕ) (X : FinitaryPerm ℕ+ → ℝ) :
    ∫ w, X w ∂grassmannianLaw n =
      ((2 : ℝ) ^ n)⁻¹ * ∑ V ∈ (positions n).powerset, X (subsetPermutation n V) := by
  rw [grassmannianLaw, integral_map (measurable_subsetPermutation n).aemeasurable
    (measurable_of_countable X).aestronglyMeasurable, integral_subsetEncoding]

end FinitaryPerm
