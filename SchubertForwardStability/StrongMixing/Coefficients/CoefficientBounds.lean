import SchubertForwardStability.StrongMixing.Coefficients.Extension
import SchubertForwardStability.StrongMixing.Coefficients.Atoms

/-! # Basic bounds and coordinate transport for lag coefficients

## Main results

* `mixingCoeff_nonneg`, `mixingCoeff_le_one`: probability-space lag coefficients lie in `[0,1]`.
* `mixingCoeff_comp_le`: measurable maps contract lag coefficients.
* `finiteMixingCoeff_comp_le`: arbitrary maps contract coefficients on finite sample spaces.
-/

open MeasureTheory

namespace StrongMixing

variable {Ω E F : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
  [MeasurableSpace F] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Every lag coefficient of a probability-space sequence is at most one. -/
theorem mixingCoeff_le_one (X : ℤ → Ω → E) (h : ℕ) : mixingCoeff μ X h ≤ 1 := by
  unfold mixingCoeff
  exact ciSup_le fun _ ↦ strongMixingCoeff_le_one μ _ _

/-- The coefficient at a fixed integer cut is bounded by the lag coefficient. -/
theorem cutCoeff_le_mixingCoeff (X : ℤ → Ω → E) (h : ℕ) (k : ℤ) :
    strongMixingCoeff μ (generatedSigma X {i | i ≤ k})
      (generatedSigma X {i | k + (h : ℤ) ≤ i}) ≤ mixingCoeff μ X h := by
  unfold mixingCoeff
  have hb : BddAbove (Set.range fun j : ℤ ↦
      strongMixingCoeff μ (generatedSigma X {i | i ≤ j})
        (generatedSigma X {i | j + (h : ℤ) ≤ i})) := ⟨1, by
    rintro _ ⟨j, rfl⟩
    exact strongMixingCoeff_le_one μ _ _⟩
  exact le_ciSup hb k

/-- Every lag coefficient of a probability-space sequence is nonnegative. -/
theorem mixingCoeff_nonneg (X : ℤ → Ω → E) (h : ℕ) : 0 ≤ mixingCoeff μ X h :=
  (strongMixingCoeff_nonneg μ _ _).trans (cutCoeff_le_mixingCoeff μ X h 0)

/-- Inclusion of all generated coordinate sigma-algebras contracts every lag coefficient. -/
theorem mixingCoeff_mono (X : ℤ → Ω → E) (Y : ℤ → Ω → F)
    (hXY : ∀ s, generatedSigma X s ≤ generatedSigma Y s) (h : ℕ) :
    mixingCoeff μ X h ≤ mixingCoeff μ Y h := by
  apply ciSup_le
  intro k
  exact (strongMixingCoeff_mono μ (hXY _) (hXY _)).trans
    (cutCoeff_le_mixingCoeff μ Y h k)

/-- Lag coefficients are nonincreasing because increasing the lag reduces each future
event sigma-algebra while leaving its past unchanged. -/
theorem mixingCoeff_antitone (X : ℤ → Ω → E) : Antitone (mixingCoeff μ X) := by
  intro h h' hh
  unfold mixingCoeff
  apply ciSup_le
  intro k
  have hfuture : generatedSigma X {i | k + (h' : ℤ) ≤ i} ≤
      generatedSigma X {i | k + (h : ℤ) ≤ i} := by
    apply generatedSigma_mono
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi ⊢
    omega
  exact (strongMixingCoeff_mono μ le_rfl hfuture).trans
    (cutCoeff_le_mixingCoeff μ X h k)

/-- A measurable coordinate map contracts every lag coefficient. -/
theorem mixingCoeff_comp_le (X : ℤ → Ω → E) (g : E → F) (hg : Measurable g) (h : ℕ) :
    mixingCoeff μ (fun i ω ↦ g (X i ω)) h ≤ mixingCoeff μ X h :=
  mixingCoeff_mono μ _ _ (fun s ↦ generatedSigma_comp_le X g hg s) h

/-- On a finite sample space, arbitrary maps on coordinate values contract all lag
coefficients without any global measurability requirement on the map. -/
theorem mixingCoeff_comp_finite_le [Finite Ω] [MeasurableSingletonClass E]
    (X : ℤ → Ω → E) (g : E → F) (h : ℕ) :
    mixingCoeff μ (fun i ω ↦ g (X i ω)) h ≤ mixingCoeff μ X h :=
  mixingCoeff_mono μ _ _ (fun s ↦ generatedSigma_comp_finite_le X (fun _ ↦ g) s) h

/-- Arbitrary coordinate maps contract finite-row coefficients on finite sample spaces,
and both outside constants may be chosen freely. -/
theorem finiteMixingCoeff_comp_le [Finite Ω] [MeasurableSingletonClass E] {N : ℕ}
    (X : Fin (N + 1) → Ω → E) (g : E → F) (x : E) (y : F) (h : ℕ) :
    finiteMixingCoeff μ (fun i ω ↦ g (X i ω)) y h ≤ finiteMixingCoeff μ X x h := by
  rw [finiteMixingCoeff_const_indep μ (fun i ω ↦ g (X i ω)) y (g x) h]
  have heq : constantExtension (fun i ω ↦ g (X i ω)) (g x) =
      fun i ω ↦ g (constantExtension X x i ω) := by
    funext i ω
    by_cases hi : 0 ≤ i ∧ i < (N + 1 : ℤ) <;> simp [constantExtension, hi]
  unfold finiteMixingCoeff
  rw [heq]
  exact mixingCoeff_comp_finite_le μ (constantExtension X x) g h

end StrongMixing
