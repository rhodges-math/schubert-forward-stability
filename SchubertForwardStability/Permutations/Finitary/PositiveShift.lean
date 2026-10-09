import SchubertForwardStability.Permutations.Finitary.EmbeddingPerm
import SchubertForwardStability.Permutations.Classes.ReducedWords

/-! # Translation of positive permutation indices

Translation by a natural offset is an embedding of the positive positions.
Permutation extension along this embedding transports adjacent generators
and their complete word products while fixing the preceding positions.
-/

namespace FinitaryPerm

/-- Translate positive positions by a natural offset. -/
def shiftPosition (m : ℕ) : ℕ+ ↪ ℕ+ where
  toFun i := ⟨m + (i : ℕ), by have hp := i.pos; omega⟩
  inj' i j h := by
    apply PNat.eq
    have he := congrArg PNat.val h
    change m + (i : ℕ) = m + (j : ℕ) at he
    omega

/-- Translation adds `m` to the natural coordinate. -/
theorem shiftPosition_val (m : ℕ) (i : ℕ+) :
    (shiftPosition m i : ℕ) = m + (i : ℕ) := rfl

/-- Translation commutes with the next positive position. -/
theorem shiftPosition_succ (m : ℕ) (i : ℕ+) :
    shiftPosition m (i + 1) = shiftPosition m i + 1 := by
  apply PNat.eq
  change m + ((i : ℕ) + 1) = (m + (i : ℕ)) + 1
  omega

/-- The translated positive positions are exactly those above the offset. -/
theorem mem_range_shiftPosition (m : ℕ) (k : ℕ+) :
    k ∈ Set.range (shiftPosition m) ↔ m < (k : ℕ) := by
  constructor
  · rintro ⟨i, rfl⟩
    rw [shiftPosition_val]
    have hp := i.pos
    omega
  · intro hk
    let i : ℕ+ := ⟨(k : ℕ) - m, by omega⟩
    refine ⟨i, ?_⟩
    apply PNat.eq
    change m + ((k : ℕ) - m) = (k : ℕ)
    omega

/-- Translate a finitary permutation, fixing the first m positions. -/
noncomputable def shiftPermHom (m : ℕ) : FinitaryPerm ℕ+ →* FinitaryPerm ℕ+ :=
  embeddingPermHom (shiftPosition m)

/-- A translated permutation acts by translated original values. -/
theorem shiftPermHom_apply (m : ℕ) (w : FinitaryPerm ℕ+) (i : ℕ+) :
    shiftPermHom m w (shiftPosition m i) = shiftPosition m (w i) :=
  embeddingPerm_apply (shiftPosition m) w i

/-- A translated permutation fixes every position at or below the offset. -/
theorem shiftPermHom_fixed (m : ℕ) (w : FinitaryPerm ℕ+) (k : ℕ+) (hk : (k : ℕ) ≤ m) :
    shiftPermHom m w k = k :=
  embeddingPerm_fixed (shiftPosition m) w k (by
    rw [mem_range_shiftPosition]
    exact not_lt_of_ge hk)

/-- Translation is injective on finitary permutations. -/
theorem shiftPermHom_injective (m : ℕ) : Function.Injective (shiftPermHom m) :=
  embeddingPerm_injective (shiftPosition m)

/-- Translating an adjacent generator gives the generator at the translated index. -/
theorem shiftPermHom_simple (m : ℕ) (i : ℕ+) :
    shiftPermHom m (simpleTransposition i) = simpleTransposition (shiftPosition m i) := by
  change embeddingPerm (shiftPosition m) (swap i (i + 1)) =
    swap (shiftPosition m i) (shiftPosition m i + 1)
  rw [embeddingPerm_swap, shiftPosition_succ]

/-- Translating all letters of a word translates the represented permutation. -/
theorem wordProduct_map_shift (m : ℕ) (word : List ℕ+) :
    wordProduct (word.map (shiftPosition m)) = shiftPermHom m (wordProduct word) := by
  induction word with
  | nil => simp only [List.map_nil, wordProduct_nil, map_one]
  | cons i word ih =>
    rw [List.map_cons, wordProduct_cons, ih, wordProduct_cons, map_mul, shiftPermHom_simple]

end FinitaryPerm
