import SchubertForwardStability.Permutations.Classes.NeighborProjection

/-! # Distinct two-letter projection cases

A projection of a distinct word contains neither retained letter more than once.
Presence of the two letters and the reversed-order flag determine it completely.
-/

namespace FinitaryPerm

/-- Reversing the names of the two retained generators leaves the projection unchanged. -/
theorem neighborProjection_comm (i j : ℕ+) (word : List ℕ+) :
    neighborProjection i j word = neighborProjection j i word := by
  simp [neighborProjection, or_comm]

/-- Projecting a distinct word to two letters yields one of the five distinct subwords. -/
theorem neighborProjection_cases (word : List ℕ+) (hN : word.Nodup) (i j : ℕ+) :
    neighborProjection i j word = [] ∨ neighborProjection i j word = [i] ∨
      neighborProjection i j word = [j] ∨ neighborProjection i j word = [i, j] ∨
        neighborProjection i j word = [j, i] := by
  have hNP : (neighborProjection i j word).Nodup := hN.filter _
  have hClass : ∀ k ∈ neighborProjection i j word, k = i ∨ k = j := by
    intro k hk
    exact of_decide_eq_true (List.mem_filter.mp hk).2
  have hSub : (neighborProjection i j word).toFinset ⊆ ({i, j} : Finset ℕ+) := by
    intro k hk
    simpa using hClass k (List.mem_toFinset.mp hk)
  have hCard := Finset.card_le_card hSub
  have hMax : ({i, j} : Finset ℕ+).card ≤ 2 := by
    by_cases hij : i = j <;> simp [hij]
  have hLen : (neighborProjection i j word).length ≤ 2 := by
    rw [← List.toFinset_card_of_nodup hNP]
    exact hCard.trans hMax
  generalize he : neighborProjection i j word = p at hNP hClass hLen ⊢
  cases p with
  | nil => exact Or.inl rfl
  | cons k p =>
    have hk : k = i ∨ k = j := hClass k (by simp)
    cases p with
    | nil => rcases hk with rfl | rfl <;> simp
    | cons l p =>
      have hp : p = [] := List.eq_nil_of_length_eq_zero (by
        simp only [List.length_cons] at hLen
        omega)
      subst p
      have hl : l = i ∨ l = j := hClass l (by simp)
      rcases hk with rfl | rfl <;> rcases hl with rfl | rfl <;> simp_all

/-- Presence and the reversed-order flag determine the projection of a distinct word. -/
theorem neighborProjection_eq_of_flags (u v : List ℕ+) (hNu : u.Nodup) (hNv : v.Nodup)
    (i j : ℕ+) (hij : i ≠ j) (hi : i ∈ u ↔ i ∈ v) (hj : j ∈ u ↔ j ∈ v)
    (hr : neighborProjection i j u = [j, i] ↔ neighborProjection i j v = [j, i]) :
    neighborProjection i j u = neighborProjection i j v := by
  have hiP : i ∈ neighborProjection i j u ↔ i ∈ neighborProjection i j v := by
    simpa [neighborProjection] using hi
  have hjP : j ∈ neighborProjection i j u ↔ j ∈ neighborProjection i j v := by
    simpa [neighborProjection] using hj
  rcases neighborProjection_cases u hNu i j with hu | hu | hu | hu | hu <;>
    rcases neighborProjection_cases v hNv i j with hv | hv | hv | hv | hv
  all_goals simp_all

end FinitaryPerm
