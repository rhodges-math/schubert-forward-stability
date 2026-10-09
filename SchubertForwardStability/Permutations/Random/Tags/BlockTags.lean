import SchubertForwardStability.Permutations.Classes.Tags.BlockTags
import SchubertForwardStability.Permutations.ForMathlib.UniformFinite
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-! # Uniform block tags and their sequential sampler

## Main definitions

The discrete tag law, presence histories, completion-weighted transition
probabilities, and the sequential suffix sampler as a probability mass function.

## Implementation notes

Sampling uses the finite completion counts. Histories remain measurable
events; conditional identities are stated only when their probability is positive.
-/

namespace FinitaryPerm

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

/-- The finite tag alphabet has the discrete measurable structure. -/
instance instMeasurableSpaceBlockTag : MeasurableSpace BlockTag := ⊤

/-- Every set of block tags is measurable. -/
instance instDiscreteMeasurableBlockTag : DiscreteMeasurableSpace BlockTag :=
  ⟨fun _ => trivial⟩

/-- The uniform measure on valid boundary-symbol words of length `m`. -/
noncomputable def tagLaw (m : ℕ) : Measure (Fin m → BlockTag) :=
  uniformOn (tagWords m : Set (Fin m → BlockTag))

/-- The uniform tag law is a probability measure, including for the empty word. -/
instance isProbabilityMeasure_tagLaw (m : ℕ) : IsProbabilityMeasure (tagLaw m) :=
  isProbabilityMeasure_uniformOn (tagWords m).finite_toSet (tagWords_nonempty m)

/-- The presence state at a positive tag position, with external state zero. -/
noncomputable def tagPresence {m : ℕ} (T : Fin m → BlockTag) (t : ℕ) : Bool :=
  if ht : 0 < t ∧ t ≤ m then decide (T ⟨t - 1, by omega⟩ ≠ .zero) else false

/-- A presence history specifies every state up to the indicated time. -/
def presenceHistory {m : ℕ} (t : ℕ) (y : ℕ → Bool) : Set (Fin m → BlockTag) :=
  {T | ∀ s ≤ t, tagPresence T s = y s}

/-- The positions whose two consecutive presence states leave a free start/continue choice. -/
noncomputable def freeTagPositions (m : ℕ) (y : ℕ → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun i => y i.val = true ∧ y (i.val + 1) = true

/-- The two-state transition probability with `m` remaining positions after the next tag. -/
noncomputable def tagKernel (m : ℕ) (a b : Bool) : ℝ :=
  if a then
    if b then (2 * (extensionCount m true : ℝ)) /
      (extensionCount m false + 2 * (extensionCount m true : ℝ))
    else (extensionCount m false : ℝ) /
      (extensionCount m false + 2 * (extensionCount m true : ℝ))
  else
    if b then (extensionCount m true : ℝ) /
      ((extensionCount m false : ℝ) + extensionCount m true)
    else (extensionCount m false : ℝ) /
      ((extensionCount m false : ℝ) + extensionCount m true)

/-- The one-step Dobrushin coefficient over the Boolean tag chain's finite time range. -/
noncomputable def tagDobrushin (n : ℕ) : ℝ :=
  sSup (((Finset.range (n - 1)).image fun t =>
    |tagKernel (n - t - 2) false false - tagKernel (n - t - 2) true false|) : Set ℝ)

/-- Applying the first `h` kernels from time `r` to a two-state row vector. -/
noncomputable def applyTagKernels (n r : ℕ) : ℕ → (Bool → ℝ) → Bool → ℝ
  | 0, p => p
  | h + 1, p => fun b => ∑ a : Bool, applyTagKernels n r h p a * tagKernel (n - r - h - 2) a b

/-- A two-state probability vector has nonnegative masses adding to one. -/
def IsTwoStateProbability (p : Bool → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a : Bool, p a = 1

/-- Every boundary state admits the all-zero suffix. -/
theorem zero_validTagSuffix (m : ℕ) (present : Bool) :
    ValidTagSuffix present (fun _ : Fin m => .zero) := by
  intro i hi
  cases hi

/-- Completion counts are positive for both boundary states. -/
theorem extensionCount_pos (m : ℕ) (present : Bool) : 0 < extensionCount m present := by
  rw [extensionCount, Finset.card_pos]
  exact ⟨fun _ => .zero, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, zero_validTagSuffix m present⟩⟩

/-- The completion weight of a candidate next tag. -/
noncomputable def tagChoiceCount (m : ℕ) (present : Bool) : BlockTag → ℕ
  | .zero => extensionCount m false
  | .start => extensionCount m true
  | .cont => if present then extensionCount m true else 0

/-- The total completion weight of all allowed next symbols. -/
noncomputable def tagChoiceTotal (m : ℕ) (present : Bool) : ℕ :=
  ∑ t : BlockTag, tagChoiceCount m present t

/-- The total completion weight is strictly positive. -/
theorem tagChoiceTotal_pos (m : ℕ) (present : Bool) : 0 < tagChoiceTotal m present := by
  exact lt_of_lt_of_le (extensionCount_pos m false)
    (Finset.single_le_sum (fun t _ => Nat.zero_le (tagChoiceCount m present t))
      (Finset.mem_univ BlockTag.zero))

/-- The completion-weighted law of the next symbol. -/
noncomputable def tagChoicePMF (m : ℕ) (present : Bool) : PMF BlockTag :=
  PMF.ofFintype (fun t => (tagChoiceCount m present t : ENNReal) /
    (tagChoiceTotal m present : ENNReal)) (by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← Nat.cast_sum]
      change (tagChoiceTotal m present : ENNReal) *
        (tagChoiceTotal m present : ENNReal)⁻¹ = 1
      exact ENNReal.mul_inv_cancel (by exact_mod_cast (tagChoiceTotal_pos m present).ne')
        (by simp))

/-- Sequentially sample a suffix with probabilities proportional to completion counts. -/
noncomputable def tagSuffixSampler : ℕ → Bool → PMF (List BlockTag)
  | 0, _ => PMF.pure []
  | m + 1, present => (tagChoicePMF m present).bind fun t =>
      (tagSuffixSampler m (decide (t ≠ .zero))).map fun word => t :: word

end FinitaryPerm
