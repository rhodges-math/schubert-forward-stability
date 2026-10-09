import SchubertForwardStability.StrongMixing.Coefficients.LawTransfer

/-!
# Invariance of mixing under countable coordinatewise almost-everywhere equality

Joint vectors of countably many AEMeasurable coordinates have the same law when
their coordinates agree almost everywhere. The comap-law identity then shows that
the Rosenblatt coefficients of the generated fields agree.
-/

open MeasureTheory

namespace StrongMixing

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- Countable AEMeasurable families equal almost everywhere coordinate by
coordinate have identical Rosenblatt coefficients between any two generated
coordinate fields. The coordinate collections may be infinite or empty. -/
theorem strongMixingCoeff_family_aeeq {ι : Type*} [Countable ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : ι → Ω → E)
    (hX : ∀ i, AEMeasurable (X i) μ) (hY : ∀ i, AEMeasurable (Y i) μ)
    (hXY : ∀ i, X i =ᵐ[μ] Y i) (s t : Set ι) :
    strongMixingCoeff μ (generatedSigma X s) (generatedSigma X t) =
      strongMixingCoeff μ (generatedSigma Y s) (generatedSigma Y t) := by
  let F (u : Set ι) := generatedSigma (fun i (z : ι → E) => z i) u
  have hF (u : Set ι) : F u ≤ (inferInstance : MeasurableSpace (ι → E)) :=
    generatedSigma_le _ u (fun i _ => measurable_pi_apply i)
  have hx : AEMeasurable (fun ω => fun i => X i ω) μ := AEMeasurable.of_eval hX
  have hy : AEMeasurable (fun ω => fun i => Y i ω) μ := AEMeasurable.of_eval hY
  have he : (fun ω => fun i => X i ω) =ᵐ[μ] (fun ω => fun i => Y i ω) := by
    filter_upwards [ae_all_iff.mpr hXY] with ω hω
    exact funext hω
  rw [generatedSigma_joint_comap X s, generatedSigma_joint_comap X t,
    generatedSigma_joint_comap Y s, generatedSigma_joint_comap Y t]
  rw [strongMixingCoeff_comap_ae μ _ hx (F s) (F t) (hF s) (hF t),
    strongMixingCoeff_comap_ae μ _ hy (F s) (F t) (hF s) (hF t), Measure.map_congr he]

/-- Coordinatewise almost-everywhere equality of two AEMeasurable integer
sequences preserves every natural-lag Rosenblatt mixing coefficient, including
lag zero. No stationarity or discrete sample-space assumption is imposed. -/
theorem mixingCoeff_aeeq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : ℤ → Ω → E) (hX : ∀ i, AEMeasurable (X i) μ)
    (hY : ∀ i, AEMeasurable (Y i) μ) (hXY : ∀ i, X i =ᵐ[μ] Y i) (h : ℕ) :
    mixingCoeff μ X h = mixingCoeff μ Y h := by
  unfold mixingCoeff
  congr 1
  funext k
  exact strongMixingCoeff_family_aeeq μ X Y hX hY hXY _ _

end StrongMixing
