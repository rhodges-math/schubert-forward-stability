import SchubertForwardStability.Permutations.Finitary.Countable
import SchubertForwardStability.Permutations.Finitary.Finite
import SchubertForwardStability.Permutations.ForMathlib.UniformFinite
import Mathlib.Probability.IdentDistrib

/-! # Uniform random finitary permutations

## Main definitions

* `unif`: the uniform measure on a finite family of finitary permutations.
* `pairLaw`: the uniform measure on ordered pairs from a finite family.

## Implementation notes

Finitary permutations on positive integers have the discrete measurable structure.
Nonempty finite families give probability measures without restricting the carrier.
-/

open MeasureTheory ProbabilityTheory

namespace FinitaryPerm

/-- Every subset of the finitary-permutation carrier is measurable. -/
instance instMeasurableSpace : MeasurableSpace (FinitaryPerm ℕ+) := ⊤

/-- The measurable structure on finitary permutations is discrete. -/
instance instDiscreteMeasurableSpace : DiscreteMeasurableSpace (FinitaryPerm ℕ+) :=
  ⟨fun _ ↦ trivial⟩

/-- The uniform law on a finite family of finitary permutations. -/
noncomputable def unif (W : Finset (FinitaryPerm ℕ+)) : Measure (FinitaryPerm ℕ+) :=
  uniformOn (W : Set (FinitaryPerm ℕ+))

/-- A nonempty finite family has a probability law. -/
theorem isProbabilityMeasure_unif {W : Finset (FinitaryPerm ℕ+)} (hW : W.Nonempty) :
    IsProbabilityMeasure (unif W) :=
  isProbabilityMeasure_uniformOn W.finite_toSet hW

/-- The uniform law on ordered pairs from the same finite family. -/
noncomputable def pairLaw (W : Finset (FinitaryPerm ℕ+)) :
    Measure (FinitaryPerm ℕ+ × FinitaryPerm ℕ+) :=
  uniformOn (W.product W : Set (FinitaryPerm ℕ+ × FinitaryPerm ℕ+))

/-- The ordered-pair law is the product of the two uniform laws. -/
theorem pairLaw_eq_prod (W : Finset (FinitaryPerm ℕ+)) :
    pairLaw W = (unif W).prod (unif W) :=
  uniformOn_finset_prod W W

/-- The ordered-pair law of a nonempty family is a probability measure. -/
theorem isProbabilityMeasure_pairLaw {W : Finset (FinitaryPerm ℕ+)} (hW : W.Nonempty) :
    IsProbabilityMeasure (pairLaw W) := by
  let := isProbabilityMeasure_unif hW
  rw [pairLaw_eq_prod]
  infer_instance

/-- The two coordinate permutations of the ordered-pair law are independent. -/
theorem indepFun_pairLaw {W : Finset (FinitaryPerm ℕ+)} (hW : W.Nonempty) :
    IndepFun Prod.fst Prod.snd (pairLaw W) := by
  let := isProbabilityMeasure_unif hW
  rw [pairLaw_eq_prod]
  exact indepFun_prod measurable_id measurable_id

/-- The first coordinate of a uniform pair has the uniform marginal law. -/
theorem identDistrib_pairLaw_fst {W : Finset (FinitaryPerm ℕ+)} (hW : W.Nonempty) :
    IdentDistrib Prod.fst id (pairLaw W) (unif W) := by
  let := isProbabilityMeasure_unif hW
  refine ⟨measurable_fst.aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [pairLaw_eq_prod, Measure.map_fst_prod, measure_univ, one_smul, Measure.map_id]

/-- The second coordinate of a uniform pair has the uniform marginal law. -/
theorem identDistrib_pairLaw_snd {W : Finset (FinitaryPerm ℕ+)} (hW : W.Nonempty) :
    IdentDistrib Prod.snd id (pairLaw W) (unif W) := by
  let := isProbabilityMeasure_unif hW
  refine ⟨measurable_snd.aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [pairLaw_eq_prod, Measure.map_snd_prod, measure_univ, one_smul, Measure.map_id]

/-- A statistic's expectation under a finite uniform permutation law is its average. -/
theorem integral_unif (W : Finset (FinitaryPerm ℕ+)) (X : FinitaryPerm ℕ+ → ℝ) :
    ∫ w, X w ∂unif W = (W.card : ℝ)⁻¹ * ∑ w ∈ W, X w :=
  integral_uniform_finset W X

/-- A pair statistic's expectation is the average over all ordered pairs. -/
theorem integral_pairLaw (W : Finset (FinitaryPerm ℕ+))
    (X : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ → ℝ) :
    ∫ p, X p ∂pairLaw W = ((W.card : ℝ) ^ 2)⁻¹ * ∑ u ∈ W, ∑ v ∈ W, X (u, v) := by
  simpa only [pairLaw, pow_two] using integral_uniform_product W W X

end FinitaryPerm
