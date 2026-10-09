import SchubertForwardStability.Permutations.Classes.Tags.TagCoordinates
import SchubertForwardStability.Permutations.Classes.Intervals.RecordSwaps

/-! # Record tests from boundary-vector representatives

Endpoint-adjacent swaps give a local record criterion for arbitrary boundary
vectors. Recovery of valid vectors then gives the same criterion on Boolean families.
-/

namespace FinitaryPerm

/-- The last position is a record exactly when the final boundary symbol is absent. -/
theorem tagRepresentative_record_last {m : ℕ} (T : Fin (m + 1) → BlockTag) :
    IsRecord (wordProduct (tagRepresentative T)) (m.succPNat + 1) ↔
      T (Fin.last m) = .zero := by
  let P : Fin m → BlockTag := fun i => T i.castSucc
  have hw : IsSupported (m.succPNat : ℕ) (wordProduct (tagRepresentative P)) :=
    tagRepresentative_supported P
  cases ht : T (Fin.last m)
  · simp only [tagRepresentative, ht]
    exact iff_of_true (hw.isRecord_above (by change m + 1 < m + 1 + 1; omega)) trivial
  · simp only [tagRepresentative, ht, wordProduct_append, wordProduct_cons,
      wordProduct_nil, mul_one]
    exact iff_of_false hw.not_record_right_last (by decide)
  · simp only [tagRepresentative, ht, wordProduct_cons]
    exact iff_of_false hw.not_record_left_last (by decide)

/-- A representative position is a record exactly at an absent predecessor or a new start. -/
theorem tagRepresentative_isRecord {m : ℕ} (T : Fin m → BlockTag) (j : ℕ+)
    (hj : (j : ℕ) ≤ m + 1) : IsRecord (wordProduct (tagRepresentative T)) j ↔
      boundarySymbol T ((j : ℕ) - 1) = .zero ∨ boundarySymbol T j = .start := by
  induction m with
  | zero =>
    have he : j = 1 := PNat.eq (by change (j : ℕ) = 1; have hp := j.pos; omega)
    subst j
    exact iff_of_true (isRecord_first _) (Or.inl (boundarySymbol_zero T))
  | succ m ih =>
    let P : Fin m → BlockTag := fun i => T i.castSucc
    have hw : IsSupported (m.succPNat : ℕ) (wordProduct (tagRepresentative P)) :=
      tagRepresentative_supported P
    by_cases hFinal : (j : ℕ) = m + 2
    · have he : j = m.succPNat + 1 := PNat.eq (by change (j : ℕ) = m + 1 + 1; omega)
      subst j
      have hPred : ((m.succPNat + 1 : ℕ+) : ℕ) - 1 = m + 1 := by
        change m + 1 + 1 - 1 = m + 1
        omega
      rw [hPred, boundarySymbol_last,
        boundarySymbol_above T (by change m + 1 < m + 1 + 1; omega)]
      simpa using tagRepresentative_record_last T
    · have hOldBound : (j : ℕ) ≤ m + 1 := by omega
      have hPrev := boundarySymbol_init T ((j : ℕ) - 1) (by omega)
      have hOld := ih P hOldBound
      by_cases hEnd : (j : ℕ) = m + 1
      · have he : j = m.succPNat := PNat.eq hEnd
        subst j
        simp only [Nat.succPNat_coe, Nat.succ_eq_add_one, Nat.add_sub_cancel] at hOld ⊢
        have hPrev' : boundarySymbol T m = boundarySymbol P m :=
          boundarySymbol_init T m le_rfl
        have hCurrent := boundarySymbol_last T
        have hAbsent := boundarySymbol_above P (Nat.lt_succ_self m)
        cases ht : T (Fin.last m)
        · simpa only [tagRepresentative, ht, hPrev', hCurrent, hAbsent] using hOld
        · simp only [tagRepresentative, ht, wordProduct_append, wordProduct_cons,
            wordProduct_nil, mul_one, hCurrent]
          exact iff_of_true hw.isRecord_simple_right (Or.inr trivial)
        · rw [tagRepresentative, ht, wordProduct_cons, hw.isRecord_simple_left _ le_rfl]
          simpa [hPrev', hCurrent, ht, hAbsent] using hOld
      · have hjLower : j < m.succPNat := by change (j : ℕ) < m + 1; omega
        have hCurrent := boundarySymbol_init T (j : ℕ) (by omega)
        cases ht : T (Fin.last m)
        · simpa only [tagRepresentative, ht, hPrev, hCurrent] using hOld
        · rw [tagRepresentative, ht, wordProduct_append, wordProduct_cons,
            wordProduct_nil, mul_one, isRecord_simple_right_below _ _ _ hjLower]
          simpa only [hPrev, hCurrent] using hOld
        · rw [tagRepresentative, ht, wordProduct_cons,
            hw.isRecord_simple_left _ hjLower.le]
          simpa only [hPrev, hCurrent] using hOld

/-- Non-record indicators of representatives are the two adjacent boundary-symbol event. -/
theorem tagRepresentative_nonRecord {m : ℕ} (T : Fin m → BlockTag) (j : ℕ+)
    (hj : (j : ℕ) ≤ m + 1) :
    (wordProduct (tagRepresentative T)).nonRecordIndicator j =
      if boundarySymbol T ((j : ℕ) - 1) ≠ .zero ∧ boundarySymbol T j ≠ .start then 1 else 0 := by
  rw [nonRecordIndicator, tagRepresentative_isRecord T j hj]
  by_cases hp : boundarySymbol T ((j : ℕ) - 1) = .zero
  · simp only [hp, true_or, ↓reduceIte, ne_eq, not_true_eq_false, false_and]
  · by_cases hc : boundarySymbol T j = .start <;> simp [hp, hc]

/-- Boolean non-record indicators are determined by neighboring selector tags. -/
theorem boolean_nonRecord_local (n : ℕ) (w : FinitaryPerm ℕ+) (hw : w ∈ boolean n)
    (j : ℕ+) (hj : (j : ℕ) ≤ n) :
    w.nonRecordIndicator j = if blockTag n w ((j : ℕ) - 1) ≠ .zero ∧
      blockTag n w j ≠ .start then 1 else 0 := by
  have hn : 1 ≤ n := (Nat.succ_le_of_lt j.pos).trans hj
  have hSize : n - 1 + 1 = n := Nat.sub_add_cancel hn
  let T := booleanTags n w
  have he : wordProduct (tagRepresentative T) = w := tagRepresentative_booleanTags n hn w hw
  have hSymbol (t : ℕ) : boundarySymbol T t = blockTag n w t := by
    have h := blockTag_tagRepresentative T (valid_booleanTags n w) t
    rw [hSize, he] at h
    exact h.symm
  have h := tagRepresentative_nonRecord T j (by simpa only [hSize] using hj)
  simpa only [he, hSymbol] using h

end FinitaryPerm
