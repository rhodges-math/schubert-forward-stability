import SchubertForwardStability.Permutations.Classes.Boolean.BooleanDistinct
import SchubertForwardStability.Permutations.Classes.Tags.BlockTags
import SchubertForwardStability.Permutations.Classes.FiniteWords

/-! # Distinct-generator representatives of boundary vectors

Generators are processed in increasing order. A start is appended to the current
word; a continuation is prepended. The resulting representative need not be the
least reduced word, but never repeats a generator.
-/

namespace FinitaryPerm

/-- An increasing-index boundary vector determines an append/prepend generator word. -/
def tagRepresentative : {m : ℕ} → (Fin m → BlockTag) → List ℕ+
  | 0, _ => []
  | m + 1, T =>
    let word := tagRepresentative (fun i : Fin m => T i.castSucc)
    let k := m.succPNat
    match T (Fin.last m) with
    | .zero => word
    | .start => word ++ [k]
    | .cont => k :: word

/-- A representative contains exactly the generators with nonzero boundary symbols. -/
theorem mem_tagRepresentative {m : ℕ} (T : Fin m → BlockTag) (k : ℕ+) :
    k ∈ tagRepresentative T ↔ ∃ i : Fin m, i.val + 1 = (k : ℕ) ∧ T i ≠ .zero := by
  induction m generalizing k with
  | zero => simp [tagRepresentative]
  | succ m ih =>
    let P : Fin m → BlockTag := fun i => T i.castSucc
    have hPrefix := ih P k
    have hNonzero : (∃ i : Fin (m + 1), i.val + 1 = (k : ℕ) ∧ T i ≠ .zero) ↔
        (∃ i : Fin m, i.val + 1 = (k : ℕ) ∧ P i ≠ .zero) ∨
          ((k : ℕ) = m + 1 ∧ T (Fin.last m) ≠ .zero) := by
      constructor
      · rintro ⟨i, hi, ht⟩
        by_cases hb : i.val < m
        · left
          exact ⟨⟨i.val, hb⟩, hi, by simpa [P] using ht⟩
        · right
          have he : i = Fin.last m := Fin.ext (by change i.val = m; omega)
          exact ⟨by omega, he ▸ ht⟩
      · rintro (⟨i, hi, ht⟩ | ⟨hk, ht⟩)
        · exact ⟨i.castSucc, hi, ht⟩
        · exact ⟨Fin.last m, hk.symm, ht⟩
    rw [hNonzero]
    have hEq : k = m.succPNat ↔ (k : ℕ) = m + 1 := by
      constructor
      · rintro rfl
        rfl
      · intro hk
        apply PNat.eq
        simpa only [Nat.succPNat_coe, Nat.succ_eq_add_one] using hk
    cases ht : T (Fin.last m) <;>
      simp [tagRepresentative, ht, ← hPrefix, P, hEq]
    all_goals exact or_comm

/-- Every generator in a size-`m` representative lies in the first `m` positions. -/
theorem tagRepresentative_bound {m : ℕ} (T : Fin m → BlockTag) (k : ℕ+)
    (hk : k ∈ tagRepresentative T) : (k : ℕ) ≤ m := by
  obtain ⟨i, hi, _⟩ := (mem_tagRepresentative T k).mp hk
  omega

/-- Boundary representatives have no repeated generators, for arbitrary symbol vectors. -/
theorem tagRepresentative_nodup {m : ℕ} (T : Fin m → BlockTag) :
    (tagRepresentative T).Nodup := by
  induction m with
  | zero => simp [tagRepresentative]
  | succ m ih =>
    let P : Fin m → BlockTag := fun i => T i.castSucc
    have hN := ih P
    have hFresh : m.succPNat ∉ tagRepresentative P := by
      intro h
      have hBound := tagRepresentative_bound P _ h
      change m + 1 ≤ m at hBound
      omega
    cases ht : T (Fin.last m)
    · simpa [tagRepresentative, ht, P] using hN
    · have hAppend : (tagRepresentative P ++ [m.succPNat]).Nodup := by
        refine List.nodup_append'.mpr ⟨hN, by simp, ?_⟩
        apply List.disjoint_left.mpr
        intro a ha hb
        have he : a = m.succPNat := List.mem_singleton.mp hb
        exact hFresh (he ▸ ha)
      simpa [tagRepresentative, ht, P] using hAppend
    · simpa [tagRepresentative, ht, P] using List.nodup_cons.mpr ⟨hFresh, hN⟩

/-- Every boundary representative is a reduced expression of a Boolean permutation. -/
theorem tagRepresentative_reduced {m : ℕ} (T : Fin m → BlockTag) :
    IsReducedWord (wordProduct (tagRepresentative T)) (tagRepresentative T) :=
  isReducedWord_of_nodup _ (tagRepresentative_nodup T)

/-- Processing a boundary vector always gives a Boolean permutation. -/
theorem tagRepresentative_boolean {m : ℕ} (T : Fin m → BlockTag) :
    IsBoolean (wordProduct (tagRepresentative T)) :=
  isBoolean_wordProduct_of_nodup _ (tagRepresentative_nodup T)

/-- A representative of length-`m` boundary vectors fixes all positions after `m+1`. -/
theorem tagRepresentative_supported {m : ℕ} (T : Fin m → BlockTag) :
    IsSupported (m + 1) (wordProduct (tagRepresentative T)) := by
  obtain ⟨word, he⟩ := exists_finiteAdjacentWord (tagRepresentative T) (by
    intro i hi
    exact Nat.lt_succ_of_le (tagRepresentative_bound T i hi))
  rw [← he, ← ofFinite_wordProduct]
  exact isSupported_ofFinite _ _

/-- Arbitrary size-`m` boundary vectors produce members of the size-`m+1` Boolean family. -/
theorem tagRepresentative_mem_boolean {m : ℕ} (T : Fin m → BlockTag) :
    wordProduct (tagRepresentative T) ∈ boolean (m + 1) :=
  (mem_boolean _ _).mpr ⟨tagRepresentative_supported T, tagRepresentative_boolean T⟩

end FinitaryPerm
