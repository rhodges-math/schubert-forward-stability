import SchubertForwardStability.Paper.Boolean.TagFields
import SchubertForwardStability.StrongMixing.Coefficients.Boundaries
import SchubertForwardStability.Permutations.Random.Tags.BooleanTagLaw
import SchubertForwardStability.StrongMixing.Coefficients.QuarterBound
import SchubertForwardStability.Paper.Boolean.SixDecay

/-! # Finite-row coefficients of Boolean non-record indicators

The exact cut estimate lifts to the supremum over all cuts of the constant extension.
The uniform decoding law then transports the bound from tag words to uniform Boolean
permutations.
-/

open MeasureTheory ProbabilityTheory FinitaryPerm StrongMixing
open scoped Classical

namespace RecordStability

/-- A relevant decoded-record cut at natural time `r` and lag at least three has
discrepancy coefficient at most one sixth to `h-2`. -/
private theorem tagRecordRow_relevant_cut (N r h : ℕ) (hh : 3 ≤ h) (hr : r + h ≤ N) :
    strongMixingCoeff (tagLaw N)
      (generatedSigma (constantExtension (tagRecordRow N) 0) {i | i ≤ (r : ℤ)})
      (generatedSigma (constantExtension (tagRecordRow N) 0) {i | (r : ℤ) + (h : ℤ) ≤ i}) ≤
      (1 / 6 : ℝ) ^ (h - 2) := by
  let m := N - (r + 1) - (h - 2)
  have hsize : N = (r + 1) + (m + (h - 2)) := by dsimp [m]; omega
  have hp : {i : ℤ | i ≤ (r : ℤ)} = {i | i ≤ ((r + 1 : ℕ) : ℤ) - 1} := by
    ext i
    simp only [Set.mem_ofPred_eq]
    omega
  have hf : {i : ℤ | (r : ℤ) + (h : ℤ) ≤ i} =
      {i | ((r + 1 : ℕ) : ℤ) + ((h - 2 : ℕ) : ℤ) + 1 ≤ i} := by
    ext i
    simp only [Set.mem_ofPred_eq]
    omega
  rw [hsize, hp, hf]
  exact tagRecordRow_cut_coeff (r + 1) m (h - 2) (by omega)

/-- The decoded non-record row under the uniform tag law has finite-row lag coefficient,
the supremum over all cuts, bounded by `(1/6)^(h-2)` for every `h>=3`. -/
theorem tagRecordRow_lag_large (N h : ℕ) (hh : 3 ≤ h) :
    finiteMixingCoeff (tagLaw N) (tagRecordRow N) 0 h ≤ (1 / 6 : ℝ) ^ (h - 2) := by
  rw [finiteMixingCoeff_eq_cuts]
  apply ciSup_le
  intro k
  by_cases hk : k.val + h ≤ N
  · rw [ite_eq_left hk]
    exact tagRecordRow_relevant_cut N k.val h hh hk
  · rw [ite_eq_right hk]
    positivity

/-- The non-record row of a uniform Boolean permutation has finite-row lag
coefficient at most `(1/6)^(h-2)` at every lag `h>=3`, including ambient size one. -/
theorem booleanNonRecord_lag_large (N h : ℕ) (hh : 3 ≤ h) :
    finiteMixingCoeff (unif (boolean (N + 1)))
      (fun i : Fin (N + 1) => fun w => w.nonRecordIndicator i.val.succPNat) 0 h ≤
      (1 / 6 : ℝ) ^ (h - 2) := by
  let Z (T : Fin N → BlockTag) := wordProduct (tagRepresentative T)
  let X (i : Fin (N + 1)) (w : FinitaryPerm ℕ+) := w.nonRecordIndicator i.val.succPNat
  have hZ : Measurable Z := measurable_of_countable Z
  have hX : ∀ i, Measurable (X i) := fun i => measurable_of_countable (X i)
  have hlaw : (tagLaw N).map Z = unif (boolean (N + 1)) := by
    have hs : N + 1 - 1 = N := by omega
    have hl := map_tagRepresentative_uniform (N + 1) (by omega)
    rw [hs] at hl
    exact hl
  have hmap := finiteMixingCoeff_map (tagLaw N) Z hZ.aemeasurable X hX 0 h
  rw [hlaw] at hmap
  rw [← hmap]
  exact tagRecordRow_lag_large N h hh

/-- The non-record indicators of a uniform Boolean permutation have their exact
one-third six-power mixing bound at every positive lag and positive ambient size. -/
theorem booleanNonRecord_mixing (N h : ℕ) (_hh : 1 ≤ h) :
    finiteMixingCoeff (unif (boolean (N + 1)))
      (fun i : Fin (N + 1) => fun w => w.nonRecordIndicator i.val.succPNat) 0 h ≤
      Real.rpow 6 (-(h : ℝ) / 3) := by
  let := isProbabilityMeasure_unif ⟨1, one_mem_boolean (N + 1)⟩
  by_cases hs : h ≤ 2
  · exact (finiteMixingCoeff_le_quarter (unif (boolean (N + 1))) _
      (fun _ => measurable_of_countable _) 0 h).trans (six_small_record_bound h hs)
  · exact (booleanNonRecord_lag_large N h (by omega)).trans
      (six_gap_decay_le h (by omega))

end RecordStability
