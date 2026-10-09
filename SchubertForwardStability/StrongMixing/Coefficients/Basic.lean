import SchubertForwardStability.StrongMixing.Coefficients.Generated
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

/-! # Rosenblatt strong-mixing coefficients

## Main definitions

* `strongMixingCoeff`: the event-discrepancy supremum of two sigma-algebras.
* `mixingCoeff`: the past/future coefficient of an integer-indexed sequence.
* `finiteMixingCoeff`: the coefficient of the constant extension of a finite row.
* `IsStrongMixing`, `IsGeometricMixing`: decay and geometric decay of the coefficients.

## Implementation notes

Coefficients use real probabilities. Probability measures make every supremum bounded.

## References

* M. Rosenblatt, *A central limit theorem and a strong mixing condition*, Proc. Nat. Acad.
  Sci. U.S.A. 42 (1956), 43-47.
-/

open MeasureTheory Filter
open scoped Topology

namespace StrongMixing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Rosenblatt's coefficient is the supremum of absolute event-probability discrepancies
over events in the two sigma-algebras. -/
noncomputable def strongMixingCoeff (μ : Measure Ω) (F G : MeasurableSpace Ω) : ℝ :=
  ⨆ A : {s : Set Ω // MeasurableSet[F] s},
    ⨆ B : {s : Set Ω // MeasurableSet[G] s},
      |μ.real (A ∩ B) - μ.real A * μ.real B|

private theorem event_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (A B : Set Ω) :
    |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ 1 := by
  have hA := measureReal_le_one (μ := μ) (s := A)
  have hB := measureReal_le_one (μ := μ) (s := B)
  have hAB := measureReal_le_one (μ := μ) (s := A ∩ B)
  have hprod : μ.real A * μ.real B ≤ 1 :=
    (mul_le_mul hA hB measureReal_nonneg (by norm_num)).trans (by norm_num)
  have hp := mul_nonneg (measureReal_nonneg (μ := μ) (s := A))
    (measureReal_nonneg (μ := μ) (s := B))
  have hi := measureReal_nonneg (μ := μ) (s := A ∩ B)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Every probability-space strong-mixing coefficient is bounded by one. -/
theorem strongMixingCoeff_le_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : MeasurableSpace Ω) : strongMixingCoeff (mΩ := mΩ) μ F G ≤ 1 :=
  ciSup_le (fun A ↦ ciSup_le (fun B ↦ event_bound (mΩ := mΩ) μ A B))

/-- Every pair of measurable events is bounded by the corresponding mixing coefficient. -/
theorem event_le_strongMixingCoeff (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : MeasurableSpace Ω) {A B : Set Ω} (hA : MeasurableSet[F] A)
    (hB : MeasurableSet[G] B) :
    |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ strongMixingCoeff (mΩ := mΩ) μ F G := by
  have hinner (A : {s : Set Ω // MeasurableSet[F] s}) :
      BddAbove (Set.range fun B : {s : Set Ω // MeasurableSet[G] s} ↦
        |μ.real (A ∩ B) - μ.real A * μ.real B|) :=
    ⟨1, by rintro _ ⟨B, rfl⟩; exact event_bound (mΩ := mΩ) μ A B⟩
  have houter : BddAbove (Set.range fun A : {s : Set Ω // MeasurableSet[F] s} ↦
      ⨆ B : {s : Set Ω // MeasurableSet[G] s},
        |μ.real (A ∩ B) - μ.real A * μ.real B|) :=
    ⟨1, by
      rintro _ ⟨A, rfl⟩
      exact ciSup_le (fun B ↦ event_bound (mΩ := mΩ) μ A B)⟩
  exact (le_ciSup (hinner ⟨A, hA⟩) ⟨B, hB⟩).trans (le_ciSup houter ⟨A, hA⟩)

/-- Strong-mixing coefficients are nonnegative. -/
theorem strongMixingCoeff_nonneg (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F G : MeasurableSpace Ω) : 0 ≤ strongMixingCoeff (mΩ := mΩ) μ F G := by
  have h := event_le_strongMixingCoeff (mΩ := mΩ) μ F G (A := ∅) (B := ∅)
    (@MeasurableSet.empty Ω F) (@MeasurableSet.empty Ω G)
  simpa using h

/-- Enlarging either event sigma-algebra can only increase its strong-mixing coefficient. -/
theorem strongMixingCoeff_mono (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F F' G G' : MeasurableSpace Ω} (hF : F ≤ F') (hG : G ≤ G') :
    strongMixingCoeff (mΩ := mΩ) μ F G ≤ strongMixingCoeff (mΩ := mΩ) μ F' G' := by
  apply ciSup_le
  intro A
  apply ciSup_le
  intro B
  exact event_le_strongMixingCoeff (mΩ := mΩ) μ F' G' (hF _ A.property) (hG _ B.property)

/-- The lag coefficient is the supremum over all integer cuts between past and future. -/
noncomputable def mixingCoeff {E : Type*} [MeasurableSpace E]
    (μ : Measure Ω) (X : ℤ → Ω → E) (h : ℕ) : ℝ :=
  ⨆ k : ℤ, strongMixingCoeff μ (generatedSigma X {i | i ≤ k})
    (generatedSigma X {i | k + (h : ℤ) ≤ i})

/-- A sequence is strongly mixing when its lag coefficients tend to zero. -/
def IsStrongMixing {E : Type*} [MeasurableSpace E]
    (μ : Measure Ω) (X : ℤ → Ω → E) : Prop :=
  Tendsto (mixingCoeff μ X) atTop (𝓝 0)

/-- A sequence is geometrically strongly mixing when positive constants bound every
positive-lag coefficient by an exponentially decaying function. -/
def IsGeometricMixing {E : Type*} [MeasurableSpace E]
    (μ : Measure Ω) (X : ℤ → Ω → E) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ h : ℕ, 1 ≤ h →
    mixingCoeff μ X h ≤ C * Real.exp (-c * h)

/-- The mixing coefficient of a finite row is that of its constant extension. -/
noncomputable def finiteMixingCoeff {N : ℕ} {E : Type*} [MeasurableSpace E]
    (μ : Measure Ω) (X : Fin (N + 1) → Ω → E) (xStar : E) (h : ℕ) : ℝ :=
  mixingCoeff μ (constantExtension X xStar) h

end StrongMixing
