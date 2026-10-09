import SchubertForwardStability.Permutations.Classes.Tags.TagRecovery

/-! # Natural coordinates of finite boundary vectors

The finite vector is extended by zero at the natural index zero and beyond its
length. Restriction and last-coordinate identities make both boundaries explicit.
-/

namespace FinitaryPerm

/-- The natural-index boundary symbol, extended by zero outside `1,...,m`. -/
def boundarySymbol {m : ℕ} (T : Fin m → BlockTag) (t : ℕ) : BlockTag :=
  if ht : 0 < t ∧ t ≤ m then T ⟨t - 1, by omega⟩ else .zero

/-- The external index zero has the absent boundary symbol. -/
@[simp]
theorem boundarySymbol_zero {m : ℕ} (T : Fin m → BlockTag) :
    boundarySymbol T 0 = .zero := by simp [boundarySymbol]

/-- Every index beyond the finite vector has the absent boundary symbol. -/
theorem boundarySymbol_above {m : ℕ} (T : Fin m → BlockTag) {t : ℕ} (ht : m < t) :
    boundarySymbol T t = .zero := by
  simp only [boundarySymbol, not_le_of_gt ht, and_false, ↓reduceDIte]

/-- A finite coordinate is read at its positive natural index. -/
theorem boundarySymbol_fin {m : ℕ} (T : Fin m → BlockTag) (i : Fin m) :
    boundarySymbol T (i.val + 1) = T i := by
  have hb : 0 < i.val + 1 ∧ i.val + 1 ≤ m := by have h := i.isLt; omega
  simp only [boundarySymbol, hb, and_self, ↓reduceDIte, Nat.add_sub_cancel]

/-- The last natural coordinate is the last finite coordinate. -/
theorem boundarySymbol_last {m : ℕ} (T : Fin (m + 1) → BlockTag) :
    boundarySymbol T (m + 1) = T (Fin.last m) := boundarySymbol_fin T (Fin.last m)

/-- Restricting away the last coordinate preserves every lower natural symbol. -/
theorem boundarySymbol_init {m : ℕ} (T : Fin (m + 1) → BlockTag) (t : ℕ) (ht : t ≤ m) :
    boundarySymbol T t = boundarySymbol (fun i : Fin m => T i.castSucc) t := by
  by_cases hp : 0 < t
  · have hb : 0 < t ∧ t ≤ m := ⟨hp, ht⟩
    have hb' : 0 < t ∧ t ≤ m + 1 := ⟨hp, ht.trans (Nat.le_succ m)⟩
    simp only [boundarySymbol, hb, hb', and_self, ↓reduceDIte]
    congr 1
  · have hz : t = 0 := Nat.eq_zero_of_not_pos hp
    rw [hz, boundarySymbol_zero, boundarySymbol_zero]

/-- The selector symbols of a valid representative agree with all natural coordinates. -/
theorem blockTag_tagRepresentative {m : ℕ} (T : Fin m → BlockTag) (hT : IsTagWord T)
    (t : ℕ) : blockTag (m + 1) (wordProduct (tagRepresentative T)) t =
      boundarySymbol T t := by
  by_cases ht : 0 < t ∧ t ≤ m
  · let i : Fin m := ⟨t - 1, by omega⟩
    have hi : i.val + 1 = t := by dsimp [i]; omega
    have he := tagRepresentative_tag T hT i
    rw [hi] at he
    simpa only [boundarySymbol, ht, and_self, ↓reduceDIte] using he
  · by_cases hz : t = 0
    · rw [hz, blockTag_zero, boundarySymbol_zero]
    · have ha : m < t := by omega
      rw [blockTag_above _ (by omega : m + 1 ≤ t), boundarySymbol_above T ha]

end FinitaryPerm
