import SchubertForwardStability.Permutations.Classes.Boolean.BooleanRecords

/-! # Overlapping interval factors of Boolean permutations

Initial and final interval factors overlap in a single position. Their product
therefore determines both factors, independently of any record-factor existence claim.
-/

namespace FinitaryPerm

open scoped Classical

/-- Two permutations agreeing away from one point also agree at that point. -/
theorem eq_of_apply_eq_off {α : Type*} [DecidableEq α] (u v : FinitaryPerm α) (a : α)
    (h : ∀ b, b ≠ a → u b = v b) : u = v := by
  apply ext
  intro b
  by_cases hb : b = a
  · subst b
    obtain ⟨c, hc⟩ := u.surjective (v a)
    by_cases hca : c = a
    · simpa only [hca] using hc
    · exact (hca (v.injective ((h c hca).symm.trans hc))).elim
  · exact h b hb

/-- Membership in a restricted Boolean family includes fixing every position outside the
interval. -/
theorem mem_booleanOn (n : ℕ) (I : Finset ℕ+) (w : FinitaryPerm ℕ+) :
    w ∈ booleanOn n I ↔ w ∈ boolean n ∧ ∀ i : ℕ+, i ∉ I → w i = i := by
  simp only [booleanOn, Finset.mem_filter]

/-- Every restricted Boolean family contains identity. -/
theorem one_mem_booleanOn (n : ℕ) (I : Finset ℕ+) :
    (1 : FinitaryPerm ℕ+) ∈ booleanOn n I :=
  (mem_booleanOn n I 1).mpr ⟨one_mem_boolean n, fun _ _ => rfl⟩

/-- A finite positive interval has exactly its lower and upper comparison conditions. -/
theorem mem_positionInterval (a n : ℕ) (i : ℕ+) :
    i ∈ positionInterval a n ↔ (i : ℕ) ≤ n ∧ a ≤ (i : ℕ) := by
  simp only [positionInterval, Finset.mem_filter, mem_positions]

/-- Restricting an ambient Boolean family to an initial interval gives that smaller family. -/
theorem booleanOn_positions (n m : ℕ) (hmn : m ≤ n) :
    booleanOn n (positions m) = boolean m := by
  ext w
  rw [mem_booleanOn, mem_boolean, mem_boolean]
  constructor
  · rintro ⟨⟨_, hBool⟩, hFix⟩
    exact ⟨fun i hi => hFix i (by rw [mem_positions]; exact not_le_of_gt hi), hBool⟩
  · rintro ⟨hSupport, hBool⟩
    exact ⟨⟨hSupport.mono hmn, hBool⟩,
      fun i hi => hSupport i (lt_of_not_ge (by simpa only [mem_positions] using hi))⟩

/-- Products of initial/final Boolean interval factors uniquely determine both factors. -/
theorem booleanInterval_product_injOn (n : ℕ) (j : ℕ+) :
    Set.InjOn (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ => p.1 * p.2)
      ((booleanOn n (positions (j : ℕ))).product
        (booleanOn n (positionInterval (j : ℕ) n)) : Set _) := by
  intro p hp q hq he
  change p ∈ (booleanOn n (positions (j : ℕ))).product
    (booleanOn n (positionInterval (j : ℕ) n)) at hp
  change q ∈ (booleanOn n (positions (j : ℕ))).product
    (booleanOn n (positionInterval (j : ℕ) n)) at hq
  have hP := Finset.mem_product.mp hp
  have hQ := Finset.mem_product.mp hq
  have hp1 := (mem_booleanOn _ _ _).mp hP.1
  have hp2 := (mem_booleanOn _ _ _).mp hP.2
  have hq1 := (mem_booleanOn _ _ _).mp hQ.1
  have hq2 := (mem_booleanOn _ _ _).mp hQ.2
  have hLeft : p.1 = q.1 := by
    refine eq_of_apply_eq_off p.1 q.1 j ?_
    intro k hk
    by_cases hLow : k < j
    · have hOutside : k ∉ positionInterval (j : ℕ) n := by
        rw [mem_positionInterval]
        exact fun h => (not_le_of_gt hLow) h.2
      have hVal := congrArg (fun w : FinitaryPerm ℕ+ => w k) he
      simpa only [mul_apply, hp2.2 k hOutside, hq2.2 k hOutside] using hVal
    · have hHigh : j < k := lt_of_le_of_ne (le_of_not_gt hLow) hk.symm
      have hOutside : k ∉ positions (j : ℕ) := by
        rw [mem_positions]
        exact not_le_of_gt hHigh
      rw [hp1.2 k hOutside, hq1.2 k hOutside]
  have hRight : p.2 = q.2 := mul_left_cancel (by simpa only [hLeft] using he)
  exact Prod.ext hLeft hRight

end FinitaryPerm
