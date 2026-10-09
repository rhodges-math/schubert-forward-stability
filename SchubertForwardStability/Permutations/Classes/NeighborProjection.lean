import SchubertForwardStability.Permutations.Classes.Boolean.BooleanLex

/-! # Neighboring-generator projections

Keeping only two neighboring generators records their relative order. Exchanging
a pair of separated generators leaves every such projection unchanged.
-/

namespace FinitaryPerm

/-- The subword containing only the two specified positive generator indices. -/
def neighborProjection (a b : ℕ+) (word : List ℕ+) : List ℕ+ :=
  word.filter fun k => decide (k = a ∨ k = b)

/-- A separated adjacent exchange preserves each neighboring-generator projection. -/
theorem WordCommutation.neighborProjection_eq {u v : List ℕ+}
    (h : WordCommutation u v) (a b : ℕ+) (hab : a + 1 = b ∨ b + 1 = a) :
    neighborProjection a b u = neighborProjection a b v := by
  obtain ⟨pre, suf, i, j, rfl, rfl, hgap⟩ := h
  have hn : ¬((i = a ∨ i = b) ∧ (j = a ∨ j = b)) := by
    rintro ⟨hi, hj⟩
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      rcases hab with hab | hab <;> rcases hgap with hgap | hgap
    all_goals
      have habN := congrArg PNat.val hab
      have hgapN := (PNat.coe_lt_coe _ _).mpr hgap
      simp only [PNat.add_coe, PNat.one_coe] at habN hgapN
      omega
  by_cases hi : i = a ∨ i = b
  · by_cases hj : j = a ∨ j = b
    · exact (hn ⟨hi, hj⟩).elim
    · simp [neighborProjection, hi, hj]
  · by_cases hj : j = a ∨ j = b
    · simp [neighborProjection, hi, hj]
    · simp [neighborProjection, hi, hj]

/-- Every sequence of separated exchanges preserves neighboring-generator order. -/
theorem commutations_neighborProjection_eq {u v : List ℕ+}
    (h : Relation.ReflTransGen WordCommutation u v) (a b : ℕ+)
    (hab : a + 1 = b ∨ b + 1 = a) :
    neighborProjection a b u = neighborProjection a b v := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (hs.neighborProjection_eq a b hab)

end FinitaryPerm
