import SchubertForwardStability.StrongMixing.Coefficients.LawTransfer
import SchubertForwardStability.StrongMixing.Coefficients.CoefficientBounds

/-! # Fiber dependence and laws of derived rows

Coordinate dependence on a finite-valued history contracts generated fields.
Composing every coordinate with one generating map preserves lag coefficients
when passing from the original probability space to the map's law.
-/

open MeasureTheory

namespace StrongMixing

/-- On a finite domain, coordinates constant on the fibers of a history generate
a sub-field of that history's pullback sigma-algebra. -/
theorem generatedSigma_fiber_le {ι Ω E F : Type*} [Finite Ω]
    [MeasurableSpace E] [MeasurableSpace F] [MeasurableSingletonClass F]
    (X : ι → Ω → E) (s : Set ι) (f : Ω → F)
    (hX : ∀ i ∈ s, ∀ ω ω', f ω = f ω' → X i ω = X i ω') :
    generatedSigma X s ≤ MeasurableSpace.comap f inferInstance := by
  apply iSup_le
  intro i A hA
  rw [measurableSet_comap_fibers]
  obtain ⟨B, _, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
  intro ω ω' he
  change X i ω ∈ B ↔ X i ω' ∈ B
  rw [hX i i.property ω ω' he]

/-- The sigma-algebra of a coordinate family composed with one generating map
is the pullback of the original coordinate sigma-algebra. -/
theorem generatedSigma_precomp {ι Ω α E : Type*} [MeasurableSpace E]
    (X : ι → α → E) (Z : Ω → α) (s : Set ι) :
    generatedSigma (fun i ω => X i (Z ω)) s = (generatedSigma X s).comap Z := by
  simp only [generatedSigma, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
    Function.comp_def]

/-- An almost-everywhere measurable generating map preserves every lag coefficient
of a measurable derived row when the target measure is its law. -/
theorem mixingCoeff_map {Ω α E : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → α) (hZ : AEMeasurable Z μ) (X : ℤ → α → E)
    (hX : ∀ i, Measurable (X i)) (h : ℕ) :
    mixingCoeff μ (fun i ω => X i (Z ω)) h = mixingCoeff (μ.map Z) X h := by
  unfold mixingCoeff
  apply iSup_congr
  intro k
  rw [generatedSigma_precomp X Z {i | i ≤ k},
    generatedSigma_precomp X Z {i | k + (h : ℤ) ≤ i}]
  exact strongMixingCoeff_comap_ae μ Z hZ _ _
    (generatedSigma_le X _ (fun i _ => hX i))
    (generatedSigma_le X _ (fun i _ => hX i))

/-- An almost-everywhere measurable generating map preserves the constant-extension
lag coefficients of a measurable finite row when passing to the map's law. -/
theorem finiteMixingCoeff_map {N : ℕ} {Ω α E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → α) (hZ : AEMeasurable Z μ)
    (X : Fin (N + 1) → α → E) (hX : ∀ i, Measurable (X i)) (xStar : E) (h : ℕ) :
    finiteMixingCoeff μ (fun i ω => X i (Z ω)) xStar h =
      finiteMixingCoeff (μ.map Z) X xStar h := by
  have he : constantExtension (fun i ω => X i (Z ω)) xStar =
      fun i ω => constantExtension X xStar i (Z ω) := by
    funext i ω
    rfl
  unfold finiteMixingCoeff
  rw [he]
  apply mixingCoeff_map μ Z hZ
  intro i
  by_cases hi : 0 ≤ i ∧ i < (N + 1 : ℤ)
  · have hfun : constantExtension X xStar i = X ⟨i.toNat, by omega⟩ := by
      funext ω
      dsimp only [constantExtension]
      rw [dite_eq_left hi]
    rw [hfun]
    exact hX _
  · have hfun : constantExtension X xStar i = fun _ => xStar := by
      funext ω
      dsimp only [constantExtension]
      rw [dite_eq_right hi]
    rw [hfun]
    exact measurable_const

end StrongMixing
