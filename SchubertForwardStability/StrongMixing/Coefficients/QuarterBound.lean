import SchubertForwardStability.StrongMixing.Coefficients.Basic
import Mathlib.Tactic

/-! # Sharp bounds for measurable event discrepancies

Measurable probability events have covariance at most one quarter in absolute value.
The bound applies to generated fields when the coordinates are measurable in the
ambient sample space. No stationarity or independence hypothesis is used.
-/

open MeasureTheory

namespace StrongMixing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Two ambient-measurable events have absolute probability discrepancy at most one quarter. -/
theorem event_le_quarter {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ 1 / 4 := by
  have ha := measureReal_nonneg (μ := μ) (s := A)
  have hb := measureReal_nonneg (μ := μ) (s := B)
  have hab := measureReal_nonneg (μ := μ) (s := A ∩ B)
  have hA1 := measureReal_le_one (μ := μ) (s := A)
  have hB1 := measureReal_le_one (μ := μ) (s := B)
  have hIA := measureReal_mono (μ := μ) (Set.inter_subset_left (s := A) (t := B))
  have hIB : μ.real (A ∩ B) ≤ μ.real B := by
    have hi := measureReal_inter_add_sdiff (μ := μ) (s := B) hA
    rw [Set.inter_comm] at hi
    linarith [measureReal_nonneg (μ := μ) (s := B \ A)]
  have hU := measureReal_union_add_inter (μ := μ) (s := A) hB
  have hU1 := measureReal_le_one (μ := μ) (s := A ∪ B)
  apply abs_le.mpr
  constructor
  · by_cases hs : μ.real A + μ.real B ≤ 1
    · have hsq := (sq_le_sq₀ (add_nonneg ha hb) (by norm_num : (0 : ℝ) ≤ 1)).mpr hs
      nlinarith [sq_nonneg (μ.real A - μ.real B)]
    · have hd : 0 ≤ (1 - μ.real A) + (1 - μ.real B) := by linarith
      have hd1 : (1 - μ.real A) + (1 - μ.real B) ≤ 1 := by linarith
      have hsq := (sq_le_sq₀ hd (by norm_num : (0 : ℝ) ≤ 1)).mpr hd1
      nlinarith [sq_nonneg (μ.real A - μ.real B)]
  · by_cases hle : μ.real A ≤ μ.real B
    · have hp := mul_le_mul_of_nonneg_left hle ha
      nlinarith [sq_nonneg (μ.real A - 1 / 2)]
    · have hp := mul_le_mul_of_nonneg_left (le_of_not_ge hle) hb
      nlinarith [sq_nonneg (μ.real B - 1 / 2)]

/-- Two sub-sigma-algebras of the ambient probability space have Rosenblatt coefficient
at most one quarter. The ambient containment ensures every event is measurable. -/
theorem strongMixingCoeff_le_quarter {F G : MeasurableSpace Ω}
    (hF : F ≤ mΩ) (hG : G ≤ mΩ) : strongMixingCoeff (mΩ := mΩ) μ F G ≤ 1 / 4 := by
  apply ciSup_le
  intro A
  apply ciSup_le
  intro B
  exact event_le_quarter (mΩ := mΩ) μ (hF _ A.property) (hG _ B.property)

/-- An ambient-measurable integer-indexed process has lag coefficients at most one quarter,
including lag zero. -/
theorem mixingCoeff_le_quarter {E : Type*} [MeasurableSpace E]
    (X : ℤ → Ω → E) (hX : ∀ i, Measurable (X i)) (h : ℕ) :
    mixingCoeff μ X h ≤ 1 / 4 := by
  apply ciSup_le
  intro k
  exact strongMixingCoeff_le_quarter (mΩ := mΩ) μ
    (generatedSigma_le X _ (fun i _ ↦ hX i))
    (generatedSigma_le X _ (fun i _ ↦ hX i))

/-- A measurable finite row has constant-extension lag coefficients at most one quarter
for every outside value and every natural lag. -/
theorem finiteMixingCoeff_le_quarter {N : ℕ} {E : Type*} [MeasurableSpace E]
    (X : Fin (N + 1) → Ω → E) (hX : ∀ i, Measurable (X i)) (xStar : E) (h : ℕ) :
    finiteMixingCoeff μ X xStar h ≤ 1 / 4 := by
  apply mixingCoeff_le_quarter
  intro i
  by_cases hi : 0 ≤ i ∧ i < (N + 1 : ℤ)
  · have he : constantExtension X xStar i = X ⟨i.toNat, by omega⟩ := by
      funext ω
      dsimp only [constantExtension]
      rw [dite_eq_left hi]
    rw [he]
    exact hX _
  · have he : constantExtension X xStar i = fun _ ↦ xStar := by
      funext ω
      dsimp only [constantExtension]
      rw [dite_eq_right hi]
    rw [he]
    exact measurable_const

end StrongMixing
