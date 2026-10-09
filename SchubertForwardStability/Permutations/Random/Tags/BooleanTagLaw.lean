import SchubertForwardStability.Permutations.ForMathlib.UniformBijection
import SchubertForwardStability.Permutations.Classes.Tags.TagRecovery
import SchubertForwardStability.Permutations.Random.Tags.BlockTags
import SchubertForwardStability.Permutations.Random.Uniform

/-! # Uniform Boolean boundary vectors

The boundary map transports uniform permutation sampling to the uniform
finite language law. Its distinct representative gives the inverse sampling map.
-/

namespace FinitaryPerm

open MeasureTheory ProbabilityTheory

/-- Uniform Boolean permutations have the uniform valid boundary-vector law. -/
theorem map_booleanTags_uniform (n : ℕ) :
    (unif (boolean n)).map (booleanTags n) = tagLaw (n - 1) :=
  map_uniformOn_finset_bij (boolean n) (tagWords (n - 1)) (booleanTags n)
    (booleanTags_bijOn n)

/-- The distinct representative is a bijection back at every positive ambient size. -/
theorem tagRepresentative_bijOn (n : ℕ) (hn : 1 ≤ n) :
    Set.BijOn (fun T => wordProduct (tagRepresentative T))
      (tagWords (n - 1) : Set (Fin (n - 1) → BlockTag))
      (boolean n : Set (FinitaryPerm ℕ+)) := by
  have hSize : n - 1 + 1 = n := Nat.sub_add_cancel hn
  refine ⟨?_, ?_, ?_⟩
  · intro T _
    change wordProduct (tagRepresentative T) ∈ boolean n
    simpa only [hSize] using tagRepresentative_mem_boolean T
  · intro T hT U hU he
    have ht := congrArg (booleanTags (n - 1 + 1)) he
    rw [booleanTags_tagRepresentative T ((mem_tagWords T).mp hT),
      booleanTags_tagRepresentative U ((mem_tagWords U).mp hU)] at ht
    exact ht
  · intro w hw
    exact ⟨booleanTags n w, booleanTags_mem n w,
      tagRepresentative_booleanTags n hn w hw⟩

/-- Uniform valid boundary vectors decode to uniform Boolean permutations. -/
theorem map_tagRepresentative_uniform (n : ℕ) (hn : 1 ≤ n) :
    (tagLaw (n - 1)).map (fun T => wordProduct (tagRepresentative T)) =
      unif (boolean n) :=
  map_uniformOn_finset_bij (tagWords (n - 1)) (boolean n)
    (fun T => wordProduct (tagRepresentative T)) (tagRepresentative_bijOn n hn)

end FinitaryPerm
