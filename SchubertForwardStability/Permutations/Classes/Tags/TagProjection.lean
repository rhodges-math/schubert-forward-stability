import SchubertForwardStability.Permutations.Classes.Tags.TagRepresentative
import SchubertForwardStability.Permutations.Classes.NeighborProjection
import SchubertForwardStability.Permutations.Classes.ProjectionWords

/-! # Projections of boundary-vector representatives

The last inserted generator cannot affect a projection onto smaller indices.
Exact nonzero-coordinate membership is retained at every earlier coordinate.
-/

namespace FinitaryPerm

/-- A coordinate's positive generator occurs exactly when its boundary symbol is nonzero. -/
theorem tagRepresentative_present {m : ℕ} (T : Fin m → BlockTag) (i : Fin m) :
    i.val.succPNat ∈ tagRepresentative T ↔ T i ≠ .zero := by
  rw [mem_tagRepresentative]
  constructor
  · rintro ⟨j, hji, hj⟩
    have he : j = i := Fin.ext (by change j.val + 1 = i.val + 1 at hji; omega)
    exact he ▸ hj
  · intro hi
    exact ⟨i, rfl, hi⟩

/-- The last boundary symbol leaves each lower-index two-letter projection unchanged. -/
theorem tagRepresentative_proj_init {m : ℕ} (T : Fin (m + 1) → BlockTag) (a b : ℕ+)
    (ha : (a : ℕ) ≤ m) (hb : (b : ℕ) ≤ m) :
    neighborProjection a b (tagRepresentative T) =
      neighborProjection a b (tagRepresentative (fun i : Fin m => T i.castSucc)) := by
  have hka : m.succPNat ≠ a := by
    intro h
    have he := congrArg PNat.val h
    change m + 1 = (a : ℕ) at he
    omega
  have hkb : m.succPNat ≠ b := by
    intro h
    have he := congrArg PNat.val h
    change m + 1 = (b : ℕ) at he
    omega
  cases ht : T (Fin.last m)
  · rw [tagRepresentative, ht]
  · simp [tagRepresentative, ht, neighborProjection, hka, hkb]
  · simp [tagRepresentative, ht, neighborProjection, hka, hkb]

/-- Removing the last symbol preserves the local validity of a boundary vector. -/
theorem isTagWord_init {m : ℕ} (T : Fin (m + 1) → BlockTag) (hT : IsTagWord T) :
    IsTagWord (fun i : Fin m => T i.castSucc) := by
  intro i hi
  rcases hT i.castSucc hi with ⟨h0, hp⟩ | ⟨j, hji, hj⟩
  · exact Or.inl ⟨h0, hp⟩
  · right
    change j.val + 1 = i.val at hji
    let k : Fin m := ⟨j.val, by have hb := i.isLt; omega⟩
    have he : k.castSucc = j := Fin.ext rfl
    exact ⟨k, hji, by change T k.castSucc ≠ .zero; rw [he]; exact hj⟩

private theorem projection_singleton (word : List ℕ+) (hN : word.Nodup) (a b : ℕ+)
    (ha : a ∉ word) (hb : b ∈ word) : neighborProjection a b word = [b] := by
  have haP : a ∉ neighborProjection a b word := by simpa [neighborProjection] using ha
  have hbP : b ∈ neighborProjection a b word := by simpa [neighborProjection] using hb
  rcases neighborProjection_cases word hN a b with h | h | h | h | h
  all_goals simp_all

/-- A valid last continuation is exactly the reversed pair involving the final generator. -/
theorem tagRepresentative_last_cont {m : ℕ} (T : Fin (m + 1) → BlockTag)
    (hT : IsTagWord T) (hm : 0 < m) :
    neighborProjection m.succPNat m.toPNat' (tagRepresentative T) =
      [m.succPNat, m.toPNat'] ↔ T (Fin.last m) = .cont := by
  let P : Fin m → BlockTag := fun i => T i.castSucc
  have hb : (m.toPNat' : ℕ) = m := PNat.toPNat'_coe hm
  have hAbsent : m.succPNat ∉ tagRepresentative P := by
    intro h
    have hBound := tagRepresentative_bound P _ h
    change m + 1 ≤ m at hBound
    omega
  have hNe : m.succPNat ≠ m.toPNat' := by
    intro h
    have he := congrArg PNat.val h
    change m + 1 = (m.toPNat' : ℕ) at he
    omega
  cases ht : T (Fin.last m)
  · constructor
    · intro h
      rw [tagRepresentative, ht] at h
      have hMem : m.succPNat ∈ neighborProjection m.succPNat m.toPNat'
          (tagRepresentative P) := by rw [h]; simp
      exact (hAbsent (List.mem_filter.mp hMem).1).elim
    · intro h
      cases h
  · constructor
    · intro h
      have hLast := congrArg List.getLast? h
      have he : m.succPNat = m.toPNat' := by
        simpa [tagRepresentative, ht, neighborProjection] using hLast
      exact (hNe he).elim
    · intro h
      cases h
  · constructor
    · intro _
      rfl
    · intro _
      have hPrev : m.toPNat' ∈ tagRepresentative P := by
        rcases hT (Fin.last m) ht with ⟨_, hp⟩ | ⟨j, hj, hNonzero⟩
        · cases hp
        · change j.val + 1 = m at hj
          let k : Fin m := ⟨j.val, by omega⟩
          have he : k.castSucc = j := Fin.ext rfl
          apply (mem_tagRepresentative P m.toPNat').mpr
          exact ⟨k, by simpa only [hb] using hj, by
            change T k.castSucc ≠ .zero
            rw [he]
            exact hNonzero⟩
      have hProj := projection_singleton _ (tagRepresentative_nodup P) _ _ hAbsent hPrev
      simpa [tagRepresentative, ht, neighborProjection, P] using
        congrArg (List.cons m.succPNat) hProj

/-- Every reversed neighboring pair recovers its valid continuation coordinate. -/
theorem tagRepresentative_cont_iff {m : ℕ} (T : Fin m → BlockTag) (hT : IsTagWord T)
    (j : ℕ+) (hj : (j : ℕ) < m) :
    neighborProjection (j + 1) j (tagRepresentative T) = [j + 1, j] ↔
      T ⟨(j : ℕ), hj⟩ = .cont := by
  induction m generalizing j with
  | zero => exact (Nat.not_lt_zero _ hj).elim
  | succ m ih =>
    by_cases hLast : (j : ℕ) = m
    · have hm : 0 < m := by rw [← hLast]; exact j.pos
      have he : j = m.toPNat' := PNat.eq (by rw [PNat.toPNat'_coe hm]; exact hLast)
      have hu : j + 1 = m.succPNat := by
        apply PNat.eq
        change (j : ℕ) + 1 = m + 1
        omega
      have hi : (⟨(j : ℕ), hj⟩ : Fin (m + 1)) = Fin.last m := Fin.ext hLast
      rw [hi, hu, he]
      exact tagRepresentative_last_cont T hT hm
    · have hLess : (j : ℕ) < m := by omega
      have ha : ((j + 1 : ℕ+) : ℕ) ≤ m := by change (j : ℕ) + 1 ≤ m; omega
      have hb : (j : ℕ) ≤ m := Nat.le_of_lt hLess
      rw [tagRepresentative_proj_init T (j + 1) j ha hb]
      exact ih (fun i : Fin m => T i.castSucc) (isTagWord_init T hT) j hLess

end FinitaryPerm
