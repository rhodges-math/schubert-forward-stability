import SchubertForwardStability.StrongMixing.Coefficients.Atoms
import SchubertForwardStability.StrongMixing.Coefficients.Basic

/-! # Mixing coefficients and joint laws

The event coefficient depends only on the law of the generating map. Joint-vector
pullbacks identify the event sigma-algebras of coordinate collections and paired rows.
-/

open MeasureTheory

namespace StrongMixing

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]

/-- Pulling back two target sigma-algebras by an almost-everywhere measurable variable
preserves their
event mixing coefficient when the target measure is the law of that variable. -/
theorem strongMixingCoeff_comap_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → E) (hZ : AEMeasurable Z μ) (F G : MeasurableSpace E)
    (hF : F ≤ mE) (hG : G ≤ mE) :
    strongMixingCoeff (mΩ := mΩ) μ (F.comap Z) (G.comap Z) =
      strongMixingCoeff (mΩ := mE) (@Measure.map Ω E mΩ mE Z μ) F G := by
  let : MeasurableSpace E := mE
  have hm : IsProbabilityMeasure (μ.map Z) :=
    (Measure.isProbabilityMeasure_map_iff hZ).mpr inferInstance
  have he {A : Set E} (hA : MeasurableSet A) :
      (μ.map Z).real A = μ.real (Z ⁻¹' A) := by
    exact congrArg ENNReal.toReal (Measure.map_apply_of_aemeasurable hZ hA)
  apply le_antisymm
  · apply ciSup_le
    intro A
    apply ciSup_le
    intro B
    obtain ⟨C, hC, hCe⟩ := MeasurableSpace.measurableSet_comap.mp A.property
    obtain ⟨D, hD, hDe⟩ := MeasurableSpace.measurableSet_comap.mp B.property
    rw [← hCe, ← hDe]
    have hb := event_le_strongMixingCoeff (mΩ := mE) (μ.map Z) F G hC hD
    rw [he (hF _ hC), he (hG _ hD), he ((hF _ hC).inter (hG _ hD))] at hb
    simpa only [Set.preimage_inter] using hb

  · apply ciSup_le
    intro A
    apply ciSup_le
    intro B
    have hA : MeasurableSet[F.comap Z] (Z ⁻¹' A.val) :=
      MeasurableSpace.measurableSet_comap.mpr ⟨A.val, A.property, rfl⟩
    have hB : MeasurableSet[G.comap Z] (Z ⁻¹' B.val) :=
      MeasurableSpace.measurableSet_comap.mpr ⟨B.val, B.property, rfl⟩
    have hb := event_le_strongMixingCoeff (mΩ := mΩ) μ (F.comap Z) (G.comap Z) hA hB
    rw [he (hF _ A.property), he (hG _ B.property),
      he ((hF _ A.property).inter (hG _ B.property))]
    simpa only [Set.preimage_inter] using hb

/-- A measurable generating map preserves the coefficient under passage to its law.
This is the measurable specialization of the almost-everywhere measurable theorem. -/
theorem strongMixingCoeff_comap (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → E) (hZ : Measurable Z) (F G : MeasurableSpace E)
    (hF : F ≤ mE) (hG : G ≤ mE) :
    strongMixingCoeff (mΩ := mΩ) μ (F.comap Z) (G.comap Z) =
      strongMixingCoeff (mΩ := mE) (@Measure.map Ω E mΩ mE Z μ) F G := by
  let : MeasurableSpace E := mE
  exact strongMixingCoeff_comap_ae (mΩ := mΩ) (mE := mE) μ Z hZ.aemeasurable F G hF hG

omit mΩ in
/-- A row's selected-coordinate sigma-algebra is the pullback of the corresponding
coordinate-evaluation sigma-algebra by its full joint vector. -/
theorem generatedSigma_joint_comap {ι : Type*} (X : ι → Ω → E) (s : Set ι) :
    generatedSigma X s = (generatedSigma (fun i (z : ι → E) ↦ z i) s).comap
      (fun ω i ↦ X i ω) := by
  simp [generatedSigma, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
    Function.comp_def]

omit mΩ in
/-- Paired coordinates generate the supremum of the separate coordinate
sigma-algebras, including when the selected index set is empty. -/
theorem generatedSigma_pair {ι F : Type*} [MeasurableSpace F]
    (X : ι → Ω → E) (Y : ι → Ω → F) (s : Set ι) :
    generatedSigma (fun i ω ↦ (X i ω, Y i ω)) s =
      generatedSigma X s ⊔ generatedSigma Y s := by
  simp [generatedSigma, Prod.instMeasurableSpace, MeasurableSpace.prod,
    MeasurableSpace.comap_sup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_sup_eq]

omit mΩ in
/-- The sigma-algebra of selected paired row coordinates is the pullback of the
product of the two evaluation-coordinate sigma-algebras by the two full row vectors. -/
theorem generatedSigma_pair_comap {ι F : Type*} [MeasurableSpace F]
    (X : ι → Ω → E) (Y : ι → Ω → F) (s : Set ι) :
    generatedSigma (fun i ω ↦ (X i ω, Y i ω)) s =
      ((generatedSigma (fun i (z : ι → E) ↦ z i) s).prod
        (generatedSigma (fun i (z : ι → F) ↦ z i) s)).comap
          (fun ω ↦ ((fun i ↦ X i ω), (fun i ↦ Y i ω))) := by
  rw [generatedSigma_pair]
  simp [generatedSigma, MeasurableSpace.prod, MeasurableSpace.comap_sup,
    MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, Function.comp_def]

end StrongMixing
