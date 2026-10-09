import SchubertForwardStability.Permutations.Classes.GrassBlocks

/-! # Multiplicity of ordered-subset encodings

Identity is encoded by exactly the initial subsets. Every nonidentity subset
permutation determines the block boundary and recovers its selected values,
so its subset encoding is unique.
-/

namespace FinitaryPerm

open scoped Classical

/-- An initial selected subset yields the identity permutation. -/
theorem grassmannianOfSubset_eq_one (n : ℕ) (V : Finset ℕ+)
    (hV : V ⊆ positions n) (hprefix : V = positions V.card) :
    grassmannianOfSubset n V hV = 1 := by
  have hc : V.card + (positions n \ V).card = n := by
    rw [Nat.add_comm, Finset.card_sdiff_add_card_eq_card hV, card_positions]
  have hfirst : (fun i : Fin V.card ↦ (⟨i.val + 1, Nat.zero_lt_succ _⟩ : ℕ+)) =
      V.orderEmbOfFin rfl := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      have hm : (⟨i.val + 1, Nat.zero_lt_succ _⟩ : ℕ+) ∈ positions V.card :=
        (mem_positions V.card _).mpr (Nat.succ_le_of_lt i.isLt)
      exact Eq.mpr (congrArg (fun S : Finset ℕ+ ↦
        (⟨i.val + 1, Nat.zero_lt_succ _⟩ : ℕ+) ∈ S) hprefix) hm
    · intro i j hij
      exact Nat.add_lt_add_right hij 1
  have hlast : (fun i : Fin (positions n \ V).card ↦
      (⟨V.card + i.val + 1, Nat.zero_lt_succ _⟩ : ℕ+)) =
      (positions n \ V).orderEmbOfFin rfl := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      apply Finset.mem_sdiff.mpr
      constructor
      · apply (mem_positions n _).mpr
        change V.card + i.val + 1 ≤ n
        have := i.isLt
        omega
      · intro hm
        have hm' := Eq.mp (congrArg (fun S : Finset ℕ+ ↦
          (⟨V.card + i.val + 1, Nat.zero_lt_succ _⟩ : ℕ+) ∈ S) hprefix) hm
        have hle := (mem_positions V.card _).mp hm'
        change V.card + i.val + 1 ≤ V.card at hle
        omega
    · intro i j hij
      change V.card + i.val + 1 < V.card + j.val + 1
      omega
  apply ext
  intro j
  change grassmannianOfSubset n V hV j = j
  by_cases hjn : (j : ℕ) ≤ n
  · by_cases hjV : (j : ℕ) ≤ V.card
    · let i : Fin V.card := ⟨(j : ℕ) - 1, by have := PNat.pos j; omega⟩
      have hj : (⟨i.val + 1, Nat.zero_lt_succ _⟩ : ℕ+) = j := by
        apply PNat.eq
        change i.val + 1 = (j : ℕ)
        dsimp only [i]
        have := PNat.pos j
        omega
      rw [← hj, grassmannianOfSubset_apply_first]
      exact (congrFun hfirst i).symm
    · let i : Fin (positions n \ V).card := ⟨(j : ℕ) - V.card - 1, by omega⟩
      have hj : (⟨V.card + i.val + 1, Nat.zero_lt_succ _⟩ : ℕ+) = j := by
        apply PNat.eq
        change V.card + i.val + 1 = (j : ℕ)
        dsimp only [i]
        omega
      rw [← hj, grassmannianOfSubset_apply_last]
      exact (congrFun hlast i).symm
  · exact isSupported_grassmannianOfSubset n V hV j (lt_of_not_ge hjn)

/-- Identity subset encodings are precisely the initial selected subsets. -/
theorem grassmannianOfSubset_eq_one_iff (n : ℕ) (V : Finset ℕ+)
    (hV : V ⊆ positions n) :
    grassmannianOfSubset n V hV = 1 ↔ V = positions V.card := by
  constructor
  · intro hw
    have h := grassmannianOfSubset_first_image n V hV
    rw [hw] at h
    change (positions V.card).image id = V at h
    simpa only [Finset.image_id] using h.symm
  · exact grassmannianOfSubset_eq_one n V hV

/-- Equal subset encodings with equal block sizes have equal selected subsets. -/
theorem grassmannianOfSubset_eq_of_card (n : ℕ) (V U : Finset ℕ+)
    (hV : V ⊆ positions n) (hU : U ⊆ positions n) (hc : V.card = U.card)
    (hw : grassmannianOfSubset n V hV = grassmannianOfSubset n U hU) : V = U := by
  calc
    V = (positions V.card).image (grassmannianOfSubset n V hV) :=
      (grassmannianOfSubset_first_image n V hV).symm
    _ = (positions U.card).image (grassmannianOfSubset n U hU) := by rw [hc, hw]
    _ = U := grassmannianOfSubset_first_image n U hU

/-- A nonidentity ordered-subset permutation has a unique selected-subset encoding. -/
theorem grassmannianOfSubset_inj_nonid (n : ℕ) (V U : Finset ℕ+)
    (hV : V ⊆ positions n) (hU : U ⊆ positions n)
    (hVne : grassmannianOfSubset n V hV ≠ 1)
    (hw : grassmannianOfSubset n V hV = grassmannianOfSubset n U hU) : V = U := by
  obtain ⟨i, hi⟩ := exists_descent_of_ne_one (grassmannianOfSubset n V hV) hVne
  have hiU : HasDescent (grassmannianOfSubset n U hU) i := hw ▸ hi
  have hc := (grassmannianOfSubset_descent_eq n V hV i hi).symm.trans
    (grassmannianOfSubset_descent_eq n U hU i hiU)
  exact grassmannianOfSubset_eq_of_card n V U hV hU hc hw

end FinitaryPerm
