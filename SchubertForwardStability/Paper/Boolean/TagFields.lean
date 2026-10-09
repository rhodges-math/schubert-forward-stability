import SchubertForwardStability.Paper.Boolean.TagMixing
import SchubertForwardStability.StrongMixing.Coefficients.FieldTransport
import SchubertForwardStability.Permutations.Classes.Tags.TagRecords

/-! # Generated-field transport for the adjacent-tag record row

Prefix and suffix fibers control the exact constant-extension fields of the
record row decoded from a tag word. The two adjacent boundary symbols account
for the loss of two units of lag in its event-mixing estimate.
-/

open MeasureTheory FinitaryPerm StrongMixing
open scoped Classical

namespace RecordStability

/-- The uniform tag law's prefix and distant suffix pullback fields have event
mixing coefficient at most one sixth to the number of omitted tags. -/
theorem tagLaw_prefix_future_coeff (t m g : ℕ) (ht : 0 < t) :
    strongMixingCoeff (tagLaw (t + (m + g)))
      (MeasurableSpace.comap
        (fun T : Fin (t + (m + g)) → BlockTag => fun i : Fin t => T (i.castAdd (m + g)))
        inferInstance)
      (MeasurableSpace.comap (fun T : Fin (t + (m + g)) → BlockTag =>
        tagDrop m g (fun j : Fin (m + g) => T (j.natAdd t))) inferInstance) ≤
      (1 / 6 : ℝ) ^ g := by
  apply ciSup_le
  intro A
  apply ciSup_le
  intro B
  obtain ⟨D, _, hD⟩ := MeasurableSpace.measurableSet_comap.mp B.property
  rw [← hD]
  exact tagLaw_past_future_discrepancy t m g ht A.val A.property D

/-- The finite non-record row of the permutation decoded from a boundary-tag word. -/
noncomputable def tagRecordRow (m : ℕ) (i : Fin (m + 1)) (T : Fin m → BlockTag) : ℕ :=
  (wordProduct (tagRepresentative T)).nonRecordIndicator i.val.succPNat

/-- Each decoded non-record coordinate is the adjacent-boundary-symbol event,
including the deterministic first coordinate and terminal external symbol. -/
theorem tagRecordRow_local (m : ℕ) (i : Fin (m + 1)) (T : Fin m → BlockTag) :
    tagRecordRow m i T = if boundarySymbol T i.val ≠ .zero ∧
      boundarySymbol T (i.val + 1) ≠ .start then 1 else 0 := by
  have h := tagRepresentative_nonRecord T i.val.succPNat
    (by change i.val + 1 ≤ m + 1; have := i.isLt; omega)
  simpa only [tagRecordRow, Nat.succPNat_coe, Nat.succ_eq_add_one,
    Nat.add_sub_cancel] using h

/-- Prefix-equal tag words have equal boundary symbols at every time through the prefix. -/
theorem boundarySymbol_prefix_eq {t s : ℕ} (T U : Fin (t + s) → BlockTag)
    (he : ∀ i : Fin t, T (i.castAdd s) = U (i.castAdd s)) (a : ℕ) (ha : a ≤ t) :
    boundarySymbol T a = boundarySymbol U a := by
  by_cases hp : 0 < a
  · have hb : 0 < a ∧ a ≤ t + s := ⟨hp, by omega⟩
    simp only [boundarySymbol, dite_eq_left hb]
    exact he ⟨a - 1, by omega⟩
  · have hz : a = 0 := by omega
    rw [hz, boundarySymbol_zero, boundarySymbol_zero]

/-- Distant-suffix-equal tag words have equal boundary symbols after the omitted prefix. -/
theorem boundarySymbol_suffix_eq {t m g : ℕ} (T U : Fin (t + (m + g)) → BlockTag)
    (he : tagDrop m g (fun j : Fin (m + g) => T (j.natAdd t)) =
      tagDrop m g (fun j : Fin (m + g) => U (j.natAdd t)))
    (a : ℕ) (ha : t + g < a) : boundarySymbol T a = boundarySymbol U a := by
  by_cases hb : a ≤ t + (m + g)
  · have hi : 0 < a ∧ a ≤ t + (m + g) := ⟨by omega, hb⟩
    let j : Fin m := ⟨a - (t + g + 1), by omega⟩
    have h := congrFun he j
    rw [tagDrop_apply, tagDrop_apply] at h
    have hj : (⟨g + j.val, by omega⟩ : Fin (m + g)).natAdd t =
        ⟨a - 1, by omega⟩ := by
      apply Fin.ext
      dsimp [j]
      omega
    simp only [boundarySymbol, dite_eq_left hi]
    simpa only [hj] using h
  · rw [boundarySymbol_above T (by omega), boundarySymbol_above U (by omega)]

/-- A decoded record-row coordinate through time `t-1` is determined by the first `t` tags. -/
theorem tagRecordRow_prefix_eq {t s : ℕ} (T U : Fin (t + s) → BlockTag)
    (he : ∀ j : Fin t, T (j.castAdd s) = U (j.castAdd s))
    (i : Fin (t + s + 1)) (hi : i.val + 1 ≤ t) :
    tagRecordRow (t + s) i T = tagRecordRow (t + s) i U := by
  rw [tagRecordRow_local, tagRecordRow_local,
    boundarySymbol_prefix_eq T U he i.val (by omega),
    boundarySymbol_prefix_eq T U he (i.val + 1) hi]

/-- A decoded record-row coordinate strictly after a prefix and gap is determined
by the retained distant suffix alone. -/
theorem tagRecordRow_suffix_eq {t m g : ℕ} (T U : Fin (t + (m + g)) → BlockTag)
    (he : tagDrop m g (fun j : Fin (m + g) => T (j.natAdd t)) =
      tagDrop m g (fun j : Fin (m + g) => U (j.natAdd t)))
    (i : Fin (t + (m + g) + 1)) (hi : t + g < i.val) :
    tagRecordRow (t + (m + g)) i T = tagRecordRow (t + (m + g)) i U := by
  rw [tagRecordRow_local, tagRecordRow_local,
    boundarySymbol_suffix_eq T U he i.val hi,
    boundarySymbol_suffix_eq T U he (i.val + 1) (by omega)]

/-- The past field of the exact constant-extended decoded record row at cut `t-1`
is contained in the first `t` tag coordinates' pullback field. -/
theorem tagRecordRow_past_field (t s : ℕ) :
    generatedSigma (constantExtension (tagRecordRow (t + s)) 0) {i | i ≤ (t : ℤ) - 1} ≤
      MeasurableSpace.comap
        (fun T : Fin (t + s) → BlockTag => fun j : Fin t => T (j.castAdd s)) inferInstance := by
  apply generatedSigma_fiber_le
  intro i hcut T U he
  simp only [Set.mem_ofPred_eq] at hcut
  dsimp only [constantExtension]
  by_cases hi : 0 ≤ i ∧ i < ((t + s : ℕ) : ℤ) + 1
  · rw [dite_eq_left hi, dite_eq_left hi]
    exact tagRecordRow_prefix_eq T U (fun j => congrFun he j) _
      (by change i.toNat + 1 ≤ t; omega)
  · rw [dite_eq_right hi, dite_eq_right hi]

/-- The future field of the exact constant-extended decoded record row beginning
at `t+g+1` is contained in the retained distant suffix pullback field. -/
theorem tagRecordRow_future_field (t m g : ℕ) :
    generatedSigma (constantExtension (tagRecordRow (t + (m + g))) 0)
      {i | (t + g + 1 : ℤ) ≤ i} ≤
      MeasurableSpace.comap (fun T : Fin (t + (m + g)) → BlockTag =>
        tagDrop m g (fun j : Fin (m + g) => T (j.natAdd t))) inferInstance := by
  apply generatedSigma_fiber_le
  intro i hcut T U he
  simp only [Set.mem_ofPred_eq] at hcut
  dsimp only [constantExtension]
  by_cases hi : 0 ≤ i ∧ i < ((t + (m + g) : ℕ) : ℤ) + 1
  · rw [dite_eq_left hi, dite_eq_left hi]
    exact tagRecordRow_suffix_eq T U he _ (by change t + g < i.toNat; omega)
  · rw [dite_eq_right hi, dite_eq_right hi]

/-- The decoded record row's exact constant-extension past/future cut at lag `g+2`
has mixing coefficient at most `(1/6)^g` under the uniform valid tag law. -/
theorem tagRecordRow_cut_coeff (t m g : ℕ) (ht : 0 < t) :
    strongMixingCoeff (tagLaw (t + (m + g)))
      (generatedSigma (constantExtension (tagRecordRow (t + (m + g))) 0)
        {i | i ≤ (t : ℤ) - 1})
      (generatedSigma (constantExtension (tagRecordRow (t + (m + g))) 0)
        {i | (t + g + 1 : ℤ) ≤ i}) ≤ (1 / 6 : ℝ) ^ g :=
  (strongMixingCoeff_mono _ (tagRecordRow_past_field t (m + g))
    (tagRecordRow_future_field t m g)).trans (tagLaw_prefix_future_coeff t m g ht)

end RecordStability
