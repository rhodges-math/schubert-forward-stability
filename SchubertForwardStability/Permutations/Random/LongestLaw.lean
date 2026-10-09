import SchubertForwardStability.Permutations.Classes.LongestClasses
import SchubertForwardStability.Permutations.Random.Uniform
import SchubertForwardStability.Permutations.ForMathlib.UniformBijection

/-! # Uniform laws under longest conjugation

Longest conjugation is an involution preserving each of the symmetric,
Grassmannian and Boolean finite families. It preserves their uniform pair laws.
-/

namespace FinitaryPerm

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- Simultaneous longest conjugation preserves the three uniform pair laws. -/
theorem identDistrib_pair_longest (n : ℕ) (W : Finset (FinitaryPerm ℕ+))
    (hW : W = symmetricGroup n ∨ W = grassmannian n ∨ W = boolean n) :
    IdentDistrib (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ =>
      (longestElement n * p.1 * longestElement n,
        longestElement n * p.2 * longestElement n)) id (pairLaw W) (pairLaw W) := by
  let f (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) :=
    (longestElement n * p.1 * longestElement n,
      longestElement n * p.2 * longestElement n)
  have hi : Function.Involutive f := by
    intro p
    dsimp only [f]
    simp only [conjugate_longest_twice]
  have hm (w : FinitaryPerm ℕ+) :
      longestElement n * w * longestElement n ∈ W ↔ w ∈ W := by
    rcases hW with rfl | rfl | rfl
    · exact mem_symmetric_conjugate_longest n w
    · exact mem_grass_conjugate_longest n w
    · exact mem_boolean_conjugate_longest n w
  have hmap : Set.MapsTo f (W.product W : Set _) (W.product W : Set _) := by
    intro p hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr ⟨(hm p.1).mpr hp₁, (hm p.2).mpr hp₂⟩
  have hbij : Set.BijOn f (W.product W : Set _) (W.product W : Set _) :=
    ⟨hmap, hi.injective.injOn, fun p hp => ⟨f p, hmap hp, hi p⟩⟩
  refine ⟨(measurable_of_countable _).aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [Measure.map_id]
  exact map_uniformOn_finset_bij (W.product W) (W.product W) f hbij

/-- Longest conjugation preserves length, the two classes and the three uniform pair laws. -/
theorem longest_class_law (n : ℕ) :
    (∀ w : FinitaryPerm ℕ+, IsSupported n w →
      (longestElement n * w * longestElement n).length = w.length ∧
      (IsBoolean (longestElement n * w * longestElement n) ↔ IsBoolean w) ∧
      (IsGrassmannian (longestElement n * w * longestElement n) ↔ IsGrassmannian w)) ∧
    ∀ W : Finset (FinitaryPerm ℕ+),
      W = symmetricGroup n ∨ W = grassmannian n ∨ W = boolean n →
      IdentDistrib (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ =>
        (longestElement n * p.1 * longestElement n,
          longestElement n * p.2 * longestElement n)) id (pairLaw W) (pairLaw W) := by
  refine ⟨fun w hw => ⟨length_conjugate_longest hw,
    isBoolean_conjugate_longest hw, isGrassmannian_conjugate_longest hw⟩, ?_⟩
  exact identDistrib_pair_longest n

end FinitaryPerm
