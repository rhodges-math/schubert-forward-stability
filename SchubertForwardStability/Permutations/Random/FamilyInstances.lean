import SchubertForwardStability.Permutations.Random.Uniform
import SchubertForwardStability.Permutations.Classes.Boolean
import SchubertForwardStability.Permutations.Classes.Grassmannian

/-! # Probability measures on finite permutation families

## Main results

The uniform laws and their independent pair laws are probability measures for
the symmetric, Grassmannian and Boolean families at every ambient size.

## Implementation notes

Each family contains the identity, including at size zero. These instances use
the existing uniform measures without defining additional probability laws.
-/

namespace FinitaryPerm

open MeasureTheory

/-- The uniform law on an ambient symmetric group is a probability measure. -/
instance instIsProbabilityUnifSymmetric (n : ℕ) :
    IsProbabilityMeasure (unif (symmetricGroup n)) :=
  isProbabilityMeasure_unif ⟨1, one_mem_symmetricGroup n⟩

/-- The independent uniform symmetric-group pair law is a probability measure. -/
instance instIsProbabilityPairSymmetric (n : ℕ) :
    IsProbabilityMeasure (pairLaw (symmetricGroup n)) :=
  isProbabilityMeasure_pairLaw ⟨1, one_mem_symmetricGroup n⟩

/-- The uniform Grassmannian law is a probability measure. -/
instance instIsProbabilityUnifGrassmannian (n : ℕ) :
    IsProbabilityMeasure (unif (grassmannian n)) :=
  isProbabilityMeasure_unif ⟨1, one_mem_grassmannian n⟩

/-- The independent uniform Grassmannian pair law is a probability measure. -/
instance instIsProbabilityPairGrassmannian (n : ℕ) :
    IsProbabilityMeasure (pairLaw (grassmannian n)) :=
  isProbabilityMeasure_pairLaw ⟨1, one_mem_grassmannian n⟩

/-- The uniform Boolean law is a probability measure. -/
instance instIsProbabilityUnifBoolean (n : ℕ) :
    IsProbabilityMeasure (unif (boolean n)) :=
  isProbabilityMeasure_unif ⟨1, one_mem_boolean n⟩

/-- The independent uniform Boolean pair law is a probability measure. -/
instance instIsProbabilityPairBoolean (n : ℕ) :
    IsProbabilityMeasure (pairLaw (boolean n)) :=
  isProbabilityMeasure_pairLaw ⟨1, one_mem_boolean n⟩

end FinitaryPerm
