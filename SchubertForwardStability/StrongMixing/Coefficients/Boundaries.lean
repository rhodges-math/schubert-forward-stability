import SchubertForwardStability.StrongMixing.Coefficients.CoefficientBounds

/-! # Trivial cuts and the finite-row coefficient formula

## Main results

* `strongMixingCoeff_bot_left`, `strongMixingCoeff_bot_right`: trivial fields have zero mixing.
* `finiteMixingCoeff_eq_cuts`: only cuts with nonempty finite past and future are relevant.
-/

open MeasureTheory

namespace StrongMixing

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A trivial first event sigma-algebra has zero strong-mixing coefficient. -/
theorem strongMixingCoeff_bot_left (F : MeasurableSpace Ω) :
    strongMixingCoeff (mΩ := mΩ) μ ⊥ F = 0 := by
  apply le_antisymm _ (strongMixingCoeff_nonneg (mΩ := mΩ) μ ⊥ F)
  apply ciSup_le
  intro A
  apply ciSup_le
  intro B
  rcases MeasurableSpace.measurableSet_bot_iff.mp A.property with hA | hA <;>
    simp [hA, probReal_univ]

/-- A trivial second event sigma-algebra has zero strong-mixing coefficient. -/
theorem strongMixingCoeff_bot_right (F : MeasurableSpace Ω) :
    strongMixingCoeff (mΩ := mΩ) μ F ⊥ = 0 := by
  apply le_antisymm _ (strongMixingCoeff_nonneg (mΩ := mΩ) μ F ⊥)
  apply ciSup_le
  intro A
  apply ciSup_le
  intro B
  rcases MeasurableSpace.measurableSet_bot_iff.mp B.property with hB | hB <;>
    simp [hB, probReal_univ]

/-- A cut strictly before a finite row has a trivial past and coefficient zero. -/
theorem cutCoeff_ext_neg {N : ℕ} (X : Fin (N + 1) → Ω → E)
    (x : E) (h : ℕ) {k : ℤ} (hk : k < 0) :
    strongMixingCoeff μ (generatedSigma (constantExtension X x) {i | i ≤ k})
      (generatedSigma (constantExtension X x) {i | k + (h : ℤ) ≤ i}) = 0 := by
  have heq := generatedSigma_ext_outside X x {i | i ≤ k}
    (fun i hi hpos ↦ by simp only [Set.mem_ofPred_eq] at hi; omega)
  rw [heq, strongMixingCoeff_bot_left]

/-- A cut whose future starts after a finite row has a trivial future and coefficient zero. -/
theorem cutCoeff_ext_after {N : ℕ} (X : Fin (N + 1) → Ω → E)
    (x : E) (h : ℕ) {k : ℤ} (hk : (N : ℤ) < k + (h : ℤ)) :
    strongMixingCoeff μ (generatedSigma (constantExtension X x) {i | i ≤ k})
      (generatedSigma (constantExtension X x) {i | k + (h : ℤ) ≤ i}) = 0 := by
  have heq := generatedSigma_ext_outside X x {i | k + (h : ℤ) ≤ i}
    (fun i hi hpos ↦ by simp only [Set.mem_ofPred_eq] at hi; omega)
  rw [heq, strongMixingCoeff_bot_right]

/-- The coefficient of a finite constant extension is the supremum of the relevant finite
cuts; all cuts with an empty past or future contribute zero. -/
theorem finiteMixingCoeff_eq_cuts {N : ℕ} (X : Fin (N + 1) → Ω → E)
    (x : E) (h : ℕ) :
    finiteMixingCoeff μ X x h = ⨆ k : Fin (N + 1),
      if (k : ℕ) + h ≤ N then
        strongMixingCoeff μ
          (generatedSigma (constantExtension X x) {i | i ≤ (k : ℤ)})
          (generatedSigma (constantExtension X x) {i | (k : ℤ) + (h : ℤ) ≤ i})
      else 0 := by
  let f (k : ℤ) := strongMixingCoeff μ
    (generatedSigma (constantExtension X x) {i | i ≤ k})
    (generatedSigma (constantExtension X x) {i | k + (h : ℤ) ≤ i})
  let g (k : Fin (N + 1)) := if (k : ℕ) + h ≤ N then f (k : ℤ) else 0
  change (⨆ k : ℤ, f k) = ⨆ k : Fin (N + 1), g k
  have hf (k : ℤ) : 0 ≤ f k := strongMixingCoeff_nonneg μ _ _
  have hg (k : Fin (N + 1)) : 0 ≤ g k := by
    dsimp [g]
    split_ifs <;> simp [hf]
  have hgbdd : BddAbove (Set.range g) := ⟨1, by
    rintro _ ⟨k, rfl⟩
    dsimp [g]
    split_ifs
    · exact strongMixingCoeff_le_one μ _ _
    · norm_num⟩
  have hgzero : 0 ≤ ⨆ k : Fin (N + 1), g k :=
    (hg 0).trans (le_ciSup hgbdd 0)
  apply le_antisymm
  · apply ciSup_le
    intro k
    by_cases hk : k < 0
    · have heq : f k = 0 := cutCoeff_ext_neg μ X x h hk
      rw [heq]
      exact hgzero
    by_cases hkh : k + (h : ℤ) ≤ N
    · let j : Fin (N + 1) := ⟨k.toNat, by omega⟩
      have hj : (j : ℤ) = k := by dsimp [j]; omega
      have hjh : (j : ℕ) + h ≤ N := by dsimp [j]; omega
      have heq : g j = f k := by simp only [g, ite_eq_left hjh, hj]
      rw [← heq]
      exact le_ciSup hgbdd j
    · have heq : f k = 0 := cutCoeff_ext_after μ X x h (lt_of_not_ge hkh)
      rw [heq]
      exact hgzero
  · apply ciSup_le
    intro k
    dsimp [g]
    split_ifs
    · exact cutCoeff_le_mixingCoeff μ (constantExtension X x) h (k : ℤ)
    · exact mixingCoeff_nonneg μ (constantExtension X x) h

end StrongMixing
