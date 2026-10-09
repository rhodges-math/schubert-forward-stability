import SchubertForwardStability.Permutations.ForMathlib.UniformPMF
import SchubertForwardStability.Permutations.Random.Tags.TagSampler
import SchubertForwardStability.Permutations.Random.Tags.BooleanTagLaw

/-! # The decoded completion-weighted sampler law

The sequential list sampler induces the uniform valid boundary-vector measure
under optional-index recovery. Its distinct permutation representative then
has the uniform Boolean permutation law, including the empty boundary word.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace FinitaryPerm

/-- Finite lists of boundary symbols have the discrete measurable structure. -/
instance instMeasurableSpaceTagList : MeasurableSpace (List BlockTag) := ⊤

/-- Every set of finite boundary-symbol lists is measurable. -/
instance instDiscreteMeasurableTagList : DiscreteMeasurableSpace (List BlockTag) :=
  ⟨fun _ => trivial⟩

/-- Recover a length-`m` vector by optional list indexing, filling missing symbols with zero. -/
def tagListVector (m : ℕ) (L : List BlockTag) : Fin m → BlockTag :=
  fun i => L[i.val]?.getD .zero

/-- Optional-index vector recovery inverts the full list of a finite vector. -/
theorem tagListVector_ofFn {m : ℕ} (T : Fin m → BlockTag) :
    tagListVector m (List.ofFn T) = T := by
  funext i
  simp [tagListVector]

private theorem tagListVector_bij (m : ℕ) :
    Set.BijOn (tagListVector m) (tagSuffixLists m false : Set (List BlockTag))
      (tagWords m : Set (Fin m → BlockTag)) := by
  rw [tagSuffixLists_false]
  refine ⟨?_, ?_, ?_⟩
  · intro L hL
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hL
    simpa only [tagListVector_ofFn, Finset.mem_coe] using hT
  · intro L hL Q hQ he
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨U, _, rfl⟩ := Finset.mem_image.mp hQ
    rw [tagListVector_ofFn, tagListVector_ofFn] at he
    exact congrArg List.ofFn he
  · intro T hT
    exact ⟨List.ofFn T, Finset.mem_image.mpr ⟨T, hT, rfl⟩, tagListVector_ofFn T⟩

/-- The completion-weighted list sampler yields the uniform valid tag-vector
measure under optional-index recovery at every length, including zero. -/
theorem map_tagSuffixSampler_vector (m : ℕ) :
    (tagSuffixSampler m false).toMeasure.map (tagListVector m) = tagLaw m := by
  rw [tagSuffixSampler_uniform, PMF.toMeasure_uniform_finset]
  exact map_uniformOn_finset_bij (tagSuffixLists m false) (tagWords m)
    (tagListVector m) (tagListVector_bij m)

/-- Decoding the completion-weighted list sampler by optional-index boundary
recovery and the distinct representative gives the uniform Boolean permutation
law at ambient size `m+1`, including the zero-length sampler. -/
theorem map_tagSuffixSampler_uniform (m : ℕ) :
    (tagSuffixSampler m false).toMeasure.map
      (fun L => wordProduct (tagRepresentative (fun i : Fin m => L[i.val]?.getD .zero))) =
      unif (boolean (m + 1)) := by
  have h := map_tagRepresentative_uniform (m + 1) (by omega)
  have hs : m + 1 - 1 = m := by omega
  rw [hs] at h
  calc
    _ = ((tagSuffixSampler m false).toMeasure.map (tagListVector m)).map
        (fun T => wordProduct (tagRepresentative T)) := by
      rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
      rfl
    _ = (tagLaw m).map (fun T => wordProduct (tagRepresentative T)) := by
      rw [map_tagSuffixSampler_vector]
    _ = _ := h

end FinitaryPerm
