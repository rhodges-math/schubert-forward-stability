import SchubertForwardStability.Paper.Boolean.TagCoefficients
import SchubertForwardStability.StrongMixing.Coefficients.CoordinateMaps
import SchubertForwardStability.StrongMixing.Coefficients.IndependentRows
import SchubertForwardStability.Paper.Boolean.Means

/-! # Mixing of independent Boolean record increments

Independence of the two permutations under the uniform pair law gives tensorization
of their non-record rows. Coordinate-dependent centering contracts their generated
fields, and the quarter bound absorbs the small lags of the paired estimate.
-/

open MeasureTheory ProbabilityTheory FinitaryPerm StrongMixing
open scoped Classical

namespace RecordStability

/-- The paired non-record indicators under the independent Boolean pair law
have coefficient bounded by twice the individual one-third six-power bound. -/
theorem booleanPairNonRecord_mixing (N h : ℕ) (hh : 1 ≤ h) :
    finiteMixingCoeff (pairLaw (boolean (N + 1)))
      (fun i : Fin (N + 1) => fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ =>
        (p.1.nonRecordIndicator i.val.succPNat, p.2.nonRecordIndicator i.val.succPNat))
      (0, 0) h ≤ 2 * Real.rpow 6 (-(h : ℝ) / 3) := by
  let μ := pairLaw (boolean (N + 1))
  let := isProbabilityMeasure_pairLaw ⟨1, one_mem_boolean (N + 1)⟩
  let R (i : Fin (N + 1)) (w : FinitaryPerm ℕ+) := w.nonRecordIndicator i.val.succPNat
  let X (i : Fin (N + 1)) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) := R i p.1
  let Y (i : Fin (N + 1)) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) := R i p.2
  have hR : ∀ i, Measurable (R i) := fun i => measurable_of_countable (R i)
  have hX : ∀ i, Measurable (X i) := fun i => (hR i).comp measurable_fst
  have hY : ∀ i, Measurable (Y i) := fun i => (hR i).comp measurable_snd
  have hi : IndepFun (fun p i => X i p) (fun p i => Y i p) μ :=
    (indepFun_pairLaw ⟨1, one_mem_boolean (N + 1)⟩).comp
      (Measurable.of_eval hR) (Measurable.of_eval hR)
  have hf : μ.map Prod.fst = unif (boolean (N + 1)) := by
    simpa only [Measure.map_id] using
      (identDistrib_pairLaw_fst ⟨1, one_mem_boolean (N + 1)⟩).map_eq
  have hs : μ.map Prod.snd = unif (boolean (N + 1)) := by
    simpa only [Measure.map_id] using
      (identDistrib_pairLaw_snd ⟨1, one_mem_boolean (N + 1)⟩).map_eq
  have hx := finiteMixingCoeff_map μ Prod.fst measurable_fst.aemeasurable R hR 0 h
  have hy := finiteMixingCoeff_map μ Prod.snd measurable_snd.aemeasurable R hR 0 h
  rw [hf] at hx
  rw [hs] at hy
  have hp := finiteMixingCoeff_pair_le μ X Y hX hY hi 0 0 h
  rw [hx, hy] at hp
  have hb := booleanNonRecord_mixing N h hh
  apply hp.trans
  simpa only [two_mul] using add_le_add hb hb

/-- Centering the Boolean increments at their individual expectations
does not increase the coefficient of the paired non-record row at any lag. -/
theorem booleanCentered_coeff_le_pair (N h : ℕ) :
    finiteMixingCoeff (pairLaw (boolean (N + 1)))
      (fun i : Fin (N + 1) => centeredBooleanStep (N + 1) i.val.succPNat) 0 h ≤
    finiteMixingCoeff (pairLaw (boolean (N + 1)))
      (fun i : Fin (N + 1) => fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ =>
        (p.1.nonRecordIndicator i.val.succPNat, p.2.nonRecordIndicator i.val.succPNat))
      (0, 0) h := by
  let := isProbabilityMeasure_pairLaw ⟨1, one_mem_boolean (N + 1)⟩
  let X (i : Fin (N + 1)) (p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+) :=
    (p.1.nonRecordIndicator i.val.succPNat, p.2.nonRecordIndicator i.val.succPNat)
  let g (i : Fin (N + 1)) (q : ℕ × ℕ) : ℝ :=
    1 - (q.1 : ℝ) - (q.2 : ℝ) -
      ∫ p, (recordWalkStep p.1 p.2 i.val.succPNat : ℝ) ∂pairLaw (boolean (N + 1))
  have hg : ∀ i, Measurable (g i) := fun i => measurable_of_countable (g i)
  have he : (fun i : Fin (N + 1) => centeredBooleanStep (N + 1) i.val.succPNat) =
      fun i p => g i (X i p) := by
    funext i p
    dsimp only [centeredBooleanStep, g, X]
    rw [recordWalkStep_eq]
    push_cast
    rfl
  rw [he]
  exact finiteMixingCoeff_family_comp_le _ X g hg (0, 0) 0 h

/-- The individually centered increments of the independent uniform Boolean
walk have the exact one-sixth six-power coefficient bound at every positive lag. -/
theorem booleanCentered_mixing (N h : ℕ) (hh : 1 ≤ h) :
    finiteMixingCoeff (pairLaw (boolean (N + 1)))
      (fun i : Fin (N + 1) => centeredBooleanStep (N + 1) i.val.succPNat) 0 h ≤
      Real.rpow 6 (-(h : ℝ) / 6) := by
  let := isProbabilityMeasure_pairLaw ⟨1, one_mem_boolean (N + 1)⟩
  by_cases hs : h ≤ 4
  · exact (finiteMixingCoeff_le_quarter (pairLaw (boolean (N + 1))) _
      (fun _ => measurable_of_countable _) 0 h).trans (six_small_pair_bound h hs)
  · exact ((booleanCentered_coeff_le_pair N h).trans
      (booleanPairNonRecord_mixing N h hh)).trans (six_pair_decay_le h (by omega))

/-- Uniform Boolean non-record indicators and centered independent-pair walk
increments satisfy the respective one-third and one-sixth six-power bounds.
The paired bound equals the geometric exponential rate with `c=log(6)/12`. -/
theorem finiteMixingCoeff_boolean_le (n h : ℕ) (hh : 1 ≤ h) :
    finiteMixingCoeff (unif (boolean (n + 2)))
      (fun i : Fin (n + 2) => fun w => w.nonRecordIndicator i.val.succPNat) 0 h ≤
        Real.rpow 6 (-(h : ℝ) / 3) ∧
    finiteMixingCoeff (pairLaw (boolean (n + 2)))
      (fun i : Fin (n + 2) => centeredBooleanStep (n + 2) i.val.succPNat) 0 h ≤
        Real.rpow 6 (-(h : ℝ) / 6) ∧
    Real.rpow 6 (-(h : ℝ) / 6) = Real.exp (-2 * (Real.log 6 / 12) * (h : ℝ)) :=
  ⟨booleanNonRecord_mixing (n + 1) h hh,
    booleanCentered_mixing (n + 1) h hh, six_mixing_rate_eq h⟩

end RecordStability
