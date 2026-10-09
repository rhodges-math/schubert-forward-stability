import SchubertForwardStability.Permutations.Random.Subsets
import SchubertForwardStability.Permutations.Classes.GrassClassification
import SchubertForwardStability.Permutations.ForMathlib.UniformEvents

/-! # Point masses of the ordered-subset probability model

The encoded law is supported on Grassmannian permutations. Identity has one
encoding for every initial subset, and nonidentity encoded values have unique
subset encodings. Every Grassmannian permutation is attained, so these counts
determine the point probabilities on the whole ambient family.

## Main results

* `grassmannianLaw_singleton_one`: identity has mass `(n+1)/2^n`.
* `grassmannianLaw_singleton_nonid`: every other Grassmannian point has mass `2^(-n)`.
* `grassmannianLaw_singleton`: the complete point-mass formula, zero outside the family.

## Implementation notes

The ambient size is natural and may be zero. The identity fiber has size `n+1`
even at the empty boundary; nonidentity encodings are unique.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace FinitaryPerm

/-- Every value of the total subset encoding is an ambient Grassmannian permutation. -/
theorem subsetPermutation_mem_grassmannian (n : ℕ) (V : Finset ℕ+) :
    subsetPermutation n V ∈ grassmannian n := by
  by_cases hV : V ⊆ positions n
  · rw [subsetPermutation_eq n V hV]
    exact grassmannianOfSubset_mem_grass n V hV
  · simp only [subsetPermutation, dite_eq_right hV]
    exact one_mem_grassmannian n

/-- The encoded probability law is almost surely in its ambient Grassmannian family. -/
theorem ae_mem_grassmannianLaw (n : ℕ) :
    ∀ᵐ w ∂grassmannianLaw n, w ∈ grassmannian n := by
  rw [grassmannianLaw]
  apply (ae_map_iff (measurable_subsetPermutation n).aemeasurable .of_discrete).mpr
  exact ae_of_all _ (subsetPermutation_mem_grassmannian n)

/-- A nonempty uniform permutation law is almost surely in its finite sampling family. -/
theorem ae_mem_unif (W : Finset (FinitaryPerm ℕ+)) (hW : W.Nonempty) :
    ∀ᵐ w ∂unif W, w ∈ W := ae_mem_uniformOn_finset W hW

/-- The admissible subsets encoding identity are exactly the initial subsets. -/
theorem subsetPermutation_one_fiber (n : ℕ) :
    ((positions n).powerset.filter fun V ↦ subsetPermutation n V = 1) =
      (Finset.range (n + 1)).image positions := by
  ext V
  constructor
  · intro h
    obtain ⟨hV, hw⟩ := Finset.mem_filter.mp h
    have hsub := Finset.mem_powerset.mp hV
    rw [subsetPermutation_eq n V hsub] at hw
    have hp := (grassmannianOfSubset_eq_one_iff n V hsub).mp hw
    apply Finset.mem_image.mpr
    refine ⟨V.card, Finset.mem_range.mpr ?_, hp.symm⟩
    have hc := Finset.card_le_card hsub
    rw [card_positions] at hc
    omega
  · intro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
    have hsub : positions k ⊆ positions n := by
      intro j hj
      exact (mem_positions n j).mpr (((mem_positions k j).mp hj).trans hkn)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr hsub, ?_⟩
    rw [subsetPermutation_eq n (positions k) hsub]
    apply grassmannianOfSubset_eq_one
    rw [card_positions]

/-- Identity has exactly `n+1` admissible subset encodings. -/
theorem card_subsetPermutation_one_fiber (n : ℕ) :
    ((positions n).powerset.filter fun V ↦ subsetPermutation n V = 1).card = n + 1 := by
  rw [subsetPermutation_one_fiber, Finset.card_image_of_injective]
  · exact Finset.card_range (n + 1)
  · intro k l h
    have hc := congrArg Finset.card h
    simpa only [card_positions] using hc

/-- Each encoded point probability is its admissible fiber cardinality divided by `2^n`. -/
theorem grassmannianLaw_singleton_count (n : ℕ) (w : FinitaryPerm ℕ+) :
    grassmannianLaw n {w} =
      (((positions n).powerset.filter fun V ↦ subsetPermutation n V = w).card : ℝ≥0∞) /
        (2 : ℝ≥0∞) ^ n := by
  rw [grassmannianLaw, Measure.map_apply (measurable_subsetPermutation n)
    (measurableSet_singleton w), subsetLaw, uniformOn_finset_event]
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.card_powerset,
    card_positions, Nat.cast_pow, Nat.cast_ofNat]

/-- Identity has probability `(n+1)/2^n` under uniform subset encoding. -/
theorem grassmannianLaw_singleton_one (n : ℕ) :
    grassmannianLaw n {1} = ((n + 1 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ n := by
  rw [grassmannianLaw_singleton_count, card_subsetPermutation_one_fiber]

/-- The real identity probability under uniform subset encoding is `(n+1)/2^n`. -/
theorem grassmannianLaw_real_one (n : ℕ) :
    (grassmannianLaw n).real {1} = ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
  rw [measureReal_def, grassmannianLaw_singleton_one]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat]

/-- Every attained nonidentity point has exactly one admissible subset encoding. -/
theorem subsetPermutation_nonid_fiber (n : ℕ) (V : Finset ℕ+)
    (hV : V ⊆ positions n) (hw : grassmannianOfSubset n V hV ≠ 1) :
    ((positions n).powerset.filter fun U ↦
      subsetPermutation n U = grassmannianOfSubset n V hV) = {V} := by
  ext U
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
  constructor
  · rintro ⟨hU, h⟩
    rw [subsetPermutation_eq n U hU] at h
    exact (grassmannianOfSubset_inj_nonid n V U hV hU hw h.symm).symm
  · intro h
    subst U
    exact ⟨hV, subsetPermutation_eq n V hV⟩

/-- An attained nonidentity point has probability `2^(-n)` under uniform subset encoding. -/
theorem grassmannianLaw_singleton_encoded (n : ℕ) (V : Finset ℕ+)
    (hV : V ⊆ positions n) (hw : grassmannianOfSubset n V hV ≠ 1) :
    grassmannianLaw n {grassmannianOfSubset n V hV} = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [grassmannianLaw_singleton_count, subsetPermutation_nonid_fiber n V hV hw]
  simp only [Finset.card_singleton, Nat.cast_one, one_div]

/-- Every nonidentity ambient Grassmannian point has probability `2^(-n)`. -/
theorem grassmannianLaw_singleton_nonid (n : ℕ) (w : FinitaryPerm ℕ+)
    (hw : w ∈ grassmannian n) (hne : w ≠ 1) :
    grassmannianLaw n {w} = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  obtain ⟨V, hV, he⟩ := exists_grassmannianOfSubset hw
  rw [he]
  exact grassmannianLaw_singleton_encoded n V hV (he ▸ hne)

/-- The real probability of a nonidentity ambient Grassmannian point is `2^(-n)`. -/
theorem grassmannianLaw_real_nonid (n : ℕ) (w : FinitaryPerm ℕ+)
    (hw : w ∈ grassmannian n) (hne : w ≠ 1) :
    (grassmannianLaw n).real {w} = ((2 : ℝ) ^ n)⁻¹ := by
  rw [measureReal_def, grassmannianLaw_singleton_nonid n w hw hne]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]

/-- Points outside the ambient Grassmannian family have zero encoded probability. -/
theorem grassmannianLaw_singleton_zero (n : ℕ) (w : FinitaryPerm ℕ+)
    (hw : w ∉ grassmannian n) : grassmannianLaw n {w} = 0 := by
  have hf : ((positions n).powerset.filter fun V ↦ subsetPermutation n V = w) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro V hV
    have he := (Finset.mem_filter.mp hV).2
    apply hw
    rw [← he]
    exact subsetPermutation_mem_grassmannian n V
  rw [grassmannianLaw_singleton_count, hf]
  simp only [Finset.card_empty, Nat.cast_zero, ENNReal.zero_div]

/-- The encoded Grassmannian law has the stated identity, nonidentity and exterior
masses. -/
theorem grassmannianLaw_singleton (n : ℕ) (w : FinitaryPerm ℕ+) :
    grassmannianLaw n {w} =
      if w = 1 then ((n + 1 : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ n
      else if w ∈ grassmannian n then ((2 : ℝ≥0∞) ^ n)⁻¹ else 0 := by
  by_cases he : w = 1
  · subst w
    rw [ite_eq_left rfl, grassmannianLaw_singleton_one]
  · rw [ite_eq_right he]
    by_cases hw : w ∈ grassmannian n
    · rw [ite_eq_left hw, grassmannianLaw_singleton_nonid n w hw he]
    · rw [ite_eq_right hw, grassmannianLaw_singleton_zero n w hw]

end FinitaryPerm
