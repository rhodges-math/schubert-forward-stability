import SchubertForwardStability.StrongMixing.Coefficients.Independence

/-! # Coordinate-dependent maps of finite rows

Each time may have its own measurable transformation. The constant
extension still contracts every generated past and future field, independently
of the outside values chosen before and after transformation.
-/

open MeasureTheory

namespace StrongMixing

/-- Coordinate-dependent measurable transformations contract the lag coefficient
of a finite row on an arbitrary probability space, with arbitrary outside values. -/
theorem finiteMixingCoeff_family_comp_le {N : ℕ} {Ω E F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin (N + 1) → Ω → E)
    (g : Fin (N + 1) → E → F) (hg : ∀ i, Measurable (g i))
    (x : E) (y : F) (h : ℕ) :
    finiteMixingCoeff μ (fun i ω => g i (X i ω)) y h ≤
      finiteMixingCoeff μ X x h := by
  have hle (s : Set (Fin (N + 1))) :
      generatedSigma (fun i ω => g i (X i ω)) s ≤ generatedSigma X s := by
    apply iSup_le
    intro i
    exact (MeasurableSpace.comap_le_comap_of_eq_comp (g i) (hg i) rfl).trans
      (comap_le_generatedSigma X i.property)
  apply ciSup_le
  intro k
  rw [generatedSigma_extension, generatedSigma_extension]
  have hb := cutCoeff_le_mixingCoeff μ (constantExtension X x) h k
  rw [generatedSigma_extension, generatedSigma_extension] at hb
  exact (strongMixingCoeff_mono μ (hle _) (hle _)).trans hb

end StrongMixing
