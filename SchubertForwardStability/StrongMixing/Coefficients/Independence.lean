import SchubertForwardStability.StrongMixing.Coefficients.Boundaries
import Mathlib.Probability.Independence.Basic

/-! # Independence and finite-row generated sigma-algebras

Independent sigma-algebras have zero Rosenblatt coefficient. Disjoint coordinate
collections of a mutually independent row generate independent sigma-algebras.
-/

open MeasureTheory ProbabilityTheory

namespace StrongMixing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Independent sigma-algebras have zero event-discrepancy coefficient. -/
theorem strongMixingCoeff_of_indep (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : MeasurableSpace Ω) (hi : Indep F G (_mΩ := mΩ) μ) :
    strongMixingCoeff (mΩ := mΩ) μ F G = 0 := by
  apply le_antisymm _ (strongMixingCoeff_nonneg (mΩ := mΩ) μ F G)
  apply ciSup_le
  intro A
  apply ciSup_le
  intro B
  have he := (hi.indepSet_of_measurableSet A.property B.property).measure_inter_eq_mul
  have hr := congrArg ENNReal.toReal he
  have heq : μ.real (A ∩ B) = μ.real A * μ.real B := by
    simpa [measureReal_def, ENNReal.toReal_mul] using hr
  simp [heq]

omit mΩ in
/-- Selected coordinates generate the same sigma-algebra as their bounded-index supremum. -/
theorem generatedSigma_eq_biSup {ι E : Type*} [MeasurableSpace E]
    (X : ι → Ω → E) (s : Set ι) :
    generatedSigma X s = ⨆ i ∈ s, MeasurableSpace.comap (X i) inferInstance := by
  apply le_antisymm
  · exact iSup_le fun i ↦ le_iSup_of_le i.val (le_iSup_of_le i.property le_rfl)
  · exact iSup_le fun i ↦ iSup_le fun hi ↦ comap_le_generatedSigma X hi

/-- Disjoint collections of measurable, mutually independent coordinates generate
independent sigma-algebras. -/
theorem indep_generatedSigma {ι E : Type*} [MeasurableSpace E]
    (μ : Measure Ω) (X : ι → Ω → E) (hX : ∀ i, Measurable (X i))
    (hi : iIndepFun X μ) {s t : Set ι} (hst : Disjoint s t) :
    Indep (generatedSigma X s) (generatedSigma X t) (_mΩ := mΩ) μ := by
  rw [generatedSigma_eq_biSup, generatedSigma_eq_biSup]
  exact indep_iSup_of_disjoint (fun i ↦ (hX i).comap_le) hi hst

omit mΩ in
/-- The sigma-algebra of selected times in a constant extension is generated exactly
by those original row coordinates whose integer indices belong to the selected set. -/
theorem generatedSigma_extension {N : ℕ} {E : Type*} [MeasurableSpace E]
    (X : Fin (N + 1) → Ω → E) (x : E) (s : Set ℤ) :
    generatedSigma (constantExtension X x) s =
      generatedSigma X {j | (j : ℤ) ∈ s} := by
  apply le_antisymm
  · apply iSup_le
    intro i
    by_cases hi : 0 ≤ i.val ∧ i.val < (N + 1 : ℤ)
    · let j : Fin (N + 1) := ⟨i.val.toNat, by omega⟩
      have hj : (j : ℤ) = i.val := by simp [j, Int.toNat_of_nonneg hi.1]
      have he : constantExtension X x i.val = X j := by
        funext ω
        simp [constantExtension, hi, j]
      rw [he]
      apply comap_le_generatedSigma X
      change (j : ℤ) ∈ s
      rw [hj]
      exact i.property
    · have he : constantExtension X x i.val = fun _ : Ω ↦ x := by
        funext ω
        simp [constantExtension, hi]
      rw [he, MeasurableSpace.comap_const]
      exact bot_le
  · apply iSup_le
    intro j
    have he : constantExtension X x (j.val : ℤ) = X j.val := by
      funext ω
      exact constantExtension_apply X x j.val ω
    rw [← he]
    exact comap_le_generatedSigma (constantExtension X x) j.property

/-- A measurable, mutually independent finite row has zero mixing coefficient at
every positive lag, including lags longer than the row. -/
theorem finiteMixingCoeff_of_iIndep {N : ℕ} {E : Type*} [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin (N + 1) → Ω → E)
    (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X μ) (x : E)
    {h : ℕ} (hh : 1 ≤ h) : finiteMixingCoeff μ X x h = 0 := by
  apply le_antisymm _ (mixingCoeff_nonneg μ (constantExtension X x) h)
  apply ciSup_le
  intro k
  rw [generatedSigma_extension, generatedSigma_extension]
  have hd : Disjoint {j : Fin (N + 1) | (j : ℤ) ≤ k}
      {j : Fin (N + 1) | k + (h : ℤ) ≤ j} := by
    rw [Set.disjoint_left]
    intro j hj ht
    simp only [Set.mem_ofPred_eq] at hj ht
    omega
  simpa only [Set.mem_ofPred_eq] using
    (strongMixingCoeff_of_indep μ _ _ (indep_generatedSigma μ X hX hi hd)).le

end StrongMixing
