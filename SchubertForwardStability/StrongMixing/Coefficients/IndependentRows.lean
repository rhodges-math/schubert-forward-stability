import SchubertForwardStability.StrongMixing.Coefficients.Independence
import SchubertForwardStability.StrongMixing.Coefficients.LawTransfer
import SchubertForwardStability.StrongMixing.Coefficients.ProductFields

/-! # Independently paired rows and independent noise

The joint law of independent rows is a product law. Product-sigma tensorization and
exact coefficient pullback then bound the mixing coefficient of paired rows by the
sum of their coefficients. Mutually independent noise contributes zero at positive lag.

## References

* R. C. Bradley, *Basic properties of strong mixing conditions. A survey and some open
  questions*, Probab. Surv. 2 (2005), 107-144, Theorem 5.1(a).
-/

open MeasureTheory ProbabilityTheory

namespace StrongMixing

variable {Ω E F : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace E] [MeasurableSpace F]

/-- Pairing two independent measurable rows increases the selected-field mixing
coefficient by at most the sum of the two row coefficients. The index set and sample
space may be arbitrary. Independence refers to the two full joint row vectors. -/
theorem row_pair_coeff_le {ι : Type*} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → E) (Y : ι → Ω → F)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hi : IndepFun (fun ω i ↦ X i ω) (fun ω i ↦ Y i ω) μ) (s t : Set ι) :
    strongMixingCoeff μ (generatedSigma (fun i ω ↦ (X i ω, Y i ω)) s)
      (generatedSigma (fun i ω ↦ (X i ω, Y i ω)) t) ≤
      strongMixingCoeff μ (generatedSigma X s) (generatedSigma X t) +
        strongMixingCoeff μ (generatedSigma Y s) (generatedSigma Y t) := by
  let RX : Ω → (ι → E) := fun ω i ↦ X i ω
  let RY : Ω → (ι → F) := fun ω i ↦ Y i ω
  let FX (u : Set ι) := generatedSigma (fun i (z : ι → E) ↦ z i) u
  let FY (u : Set ι) := generatedSigma (fun i (z : ι → F) ↦ z i) u
  have hx : Measurable RX := Measurable.of_eval hX
  have hy : Measurable RY := Measurable.of_eval hY
  have hFX (u : Set ι) : FX u ≤ (inferInstance : MeasurableSpace (ι → E)) :=
    generatedSigma_le _ u (fun i _ ↦ measurable_pi_apply i)
  have hFY (u : Set ι) : FY u ≤ (inferInstance : MeasurableSpace (ι → F)) :=
    generatedSigma_le _ u (fun i _ ↦ measurable_pi_apply i)
  have hpx : IsProbabilityMeasure (μ.map RX) :=
    (Measure.isProbabilityMeasure_map_iff hx.aemeasurable).mpr inferInstance
  have hpy : IsProbabilityMeasure (μ.map RY) :=
    (Measure.isProbabilityMeasure_map_iff hy.aemeasurable).mpr inferInstance
  have heX : strongMixingCoeff μ (generatedSigma X s) (generatedSigma X t) =
      strongMixingCoeff (μ.map RX) (FX s) (FX t) := by
    rw [generatedSigma_joint_comap X s, generatedSigma_joint_comap X t]
    exact strongMixingCoeff_comap μ RX hx (FX s) (FX t) (hFX s) (hFX t)
  have heY : strongMixingCoeff μ (generatedSigma Y s) (generatedSigma Y t) =
      strongMixingCoeff (μ.map RY) (FY s) (FY t) := by
    rw [generatedSigma_joint_comap Y s, generatedSigma_joint_comap Y t]
    exact strongMixingCoeff_comap μ RY hy (FY s) (FY t) (hFY s) (hFY t)
  rw [heX, heY, generatedSigma_pair_comap X Y s, generatedSigma_pair_comap X Y t]
  rw [strongMixingCoeff_comap μ (fun ω ↦ (RX ω, RY ω)) (hx.prodMk hy)
    ((FX s).prod (FY s)) ((FX t).prod (FY t))
    (product_fields_mono (hFX s) (hFY s)) (product_fields_mono (hFX t) (hFY t))]
  rw [hi.map_prod_eq_prod_map_map hx.aemeasurable hy.aemeasurable]
  exact strongMixingCoeff_prod_le (μ.map RX) (μ.map RY) (FX s) (FX t) (FY s) (FY t)
    (hFX s) (hFX t) (hFY s) (hFY t)

/-- Pairing two independent measurable finite rows bounds every natural-lag
coefficient by the sum of their separate coefficients (Bradley, Theorem 5.1(a)).
The outside constants of the two rows are paired in the new row. -/
theorem finiteMixingCoeff_pair_le {N : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin (N + 1) → Ω → E) (Y : Fin (N + 1) → Ω → F)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hi : IndepFun (fun ω i ↦ X i ω) (fun ω i ↦ Y i ω) μ)
    (x : E) (y : F) (h : ℕ) :
    finiteMixingCoeff μ (fun i ω ↦ (X i ω, Y i ω)) (x, y) h ≤
      finiteMixingCoeff μ X x h + finiteMixingCoeff μ Y y h := by
  apply ciSup_le
  intro k
  rw [generatedSigma_extension, generatedSigma_extension]
  have hp := row_pair_coeff_le μ X Y hX hY hi
    {j | (j : ℤ) ≤ k} {j | k + (h : ℤ) ≤ j}
  apply hp.trans
  apply add_le_add
  · have hb := cutCoeff_le_mixingCoeff μ (constantExtension X x) h k
    rw [generatedSigma_extension, generatedSigma_extension] at hb
    exact hb
  · have hb := cutCoeff_le_mixingCoeff μ (constantExtension Y y) h k
    rw [generatedSigma_extension, generatedSigma_extension] at hb
    exact hb

/-- Pairing a measurable finite row with mutually independent noise independent
of the full row preserves the positive-lag mixing coefficient exactly. Projection
of each selected joint sigma field onto the original row proves the reverse bound,
so no finiteness or discreteness of the sample space is needed. -/
theorem finiteMixingCoeff_pair_noise_eq {N : ℕ} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Fin (N + 1) → Ω → E)
    (ε : Fin (N + 1) → Ω → F) (hX : ∀ i, Measurable (X i))
    (hε : ∀ i, Measurable (ε i))
    (hi : IndepFun (fun ω i ↦ X i ω) (fun ω i ↦ ε i ω) μ)
    (hεi : iIndepFun ε μ) (x : E) (e : F) {h : ℕ} (hh : 1 ≤ h) :
    finiteMixingCoeff μ (fun i ω ↦ (X i ω, ε i ω)) (x, e) h =
      finiteMixingCoeff μ X x h := by
  apply le_antisymm
  · have hp := finiteMixingCoeff_pair_le μ X ε hX hε hi x e h
    simpa [finiteMixingCoeff_of_iIndep μ ε hε hεi e hh] using hp
  · apply ciSup_le
    intro k
    rw [generatedSigma_extension, generatedSigma_extension]
    have hp := cutCoeff_le_mixingCoeff μ
      (constantExtension (fun i ω ↦ (X i ω, ε i ω)) (x, e)) h k
    rw [generatedSigma_extension, generatedSigma_extension] at hp
    refine (strongMixingCoeff_mono μ ?_ ?_).trans hp
    · rw [generatedSigma_pair]
      exact le_sup_left
    · rw [generatedSigma_pair]
      exact le_sup_left

/-- On a finite sample space, arbitrary coordinate maps of a row and independent
mutually independent noise do not increase positive-lag mixing. No global measurability
of the coordinate map is required. -/
theorem finiteMixingCoeff_noise_le {N : ℕ} {G : Type*} [MeasurableSpace G]
    [Finite Ω] [MeasurableSingletonClass E] [MeasurableSingletonClass F]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin (N + 1) → Ω → E) (ε : Fin (N + 1) → Ω → F)
    (hX : ∀ i, Measurable (X i)) (hε : ∀ i, Measurable (ε i))
    (hi : IndepFun (fun ω i ↦ X i ω) (fun ω i ↦ ε i ω) μ)
    (hεi : iIndepFun ε μ) (g : E → F → G) (x : E) (e : F) (z : G)
    {h : ℕ} (hh : 1 ≤ h) :
    finiteMixingCoeff μ (fun i ω ↦ g (X i ω) (ε i ω)) z h ≤
      finiteMixingCoeff μ X x h := by
  have hc := finiteMixingCoeff_comp_le μ (fun i ω ↦ (X i ω, ε i ω))
    (fun p ↦ g p.1 p.2) (x, e) z h
  have hp := finiteMixingCoeff_pair_le μ X ε hX hε hi x e h
  rw [finiteMixingCoeff_of_iIndep μ ε hε hεi e hh, add_zero] at hp
  exact hc.trans hp

end StrongMixing
