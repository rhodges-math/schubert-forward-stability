import SchubertForwardStability.Permutations.Classes.Grassmannian
import SchubertForwardStability.Permutations.Statistics.DescentOrder

/-! # Increasing blocks of subset permutations

## Main statements

The first block recovers its selected subset. Both blocks are strictly increasing,
so the only possible descent is at the block boundary. Every subset permutation
is Grassmannian, and a nonidentity one has a descent at precisely that boundary.
-/

namespace FinitaryPerm

open scoped Classical

/-- The values in the first block recover the selected subset exactly. -/
theorem grassmannianOfSubset_first_image (n : ℕ) (V : Finset ℕ+)
    (hV : V ⊆ positions n) :
    (positions V.card).image (grassmannianOfSubset n V hV) = V := by
  calc
    (positions V.card).image (grassmannianOfSubset n V hV) =
        Finset.univ.image (V.orderEmbOfFin rfl) := by
      rw [positions, Finset.image_image]
      congr 1
      funext i
      exact grassmannianOfSubset_apply_first n V hV i
    _ = V := by
      apply Finset.coe_injective
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Finset.range_orderEmbOfFin]

/-- Selected values appear in strictly increasing order in the first block. -/
theorem grassmannianOfSubset_first_mono (n : ℕ) (V : Finset ℕ+)
    (hV : V ⊆ positions n) :
    StrictMono (fun i : Fin V.card ↦
      grassmannianOfSubset n V hV ⟨i.val + 1, Nat.zero_lt_succ _⟩) := by
  simpa only [grassmannianOfSubset_apply_first, Finset.coe_orderIsoOfFin_apply]
    using (V.orderEmbOfFin rfl).strictMono

/-- Complement values appear in strictly increasing order in the second block. -/
theorem grassmannianOfSubset_last_mono (n : ℕ) (V : Finset ℕ+)
    (hV : V ⊆ positions n) :
    StrictMono (fun i : Fin (positions n \ V).card ↦
      grassmannianOfSubset n V hV ⟨V.card + i.val + 1, Nat.zero_lt_succ _⟩) := by
  simpa only [grassmannianOfSubset_apply_last, Finset.coe_orderIsoOfFin_apply]
    using ((positions n \ V).orderEmbOfFin rfl).strictMono

/-- Every descent of a subset permutation is at the boundary of its two blocks. -/
theorem grassmannianOfSubset_descent_eq (n : ℕ) (V : Finset ℕ+)
    (hV : V ⊆ positions n) (i : ℕ+) (hi : HasDescent (grassmannianOfSubset n V hV) i) :
    (i : ℕ) = V.card := by
  have hin : (i : ℕ) < n := (isSupported_grassmannianOfSubset n V hV).descent_lt hi
  have hc : V.card + (positions n \ V).card = n := by
    rw [Nat.add_comm, Finset.card_sdiff_add_card_eq_card hV, card_positions]
  by_contra hne
  have hinc : grassmannianOfSubset n V hV i < grassmannianOfSubset n V hV (i + 1) := by
    rcases lt_or_gt_of_ne hne with hfirst | hlast
    · have h := grassmannianOfSubset_first_mono n V hV
        (a := ⟨(i : ℕ) - 1, by omega⟩) (b := ⟨(i : ℕ), hfirst⟩) (by
          change (i : ℕ) - 1 < (i : ℕ)
          have := PNat.pos i
          omega)
      convert h using 1
      · congr 1
        apply PNat.eq
        change (i : ℕ) = (i : ℕ) - 1 + 1
        have := PNat.pos i
        omega
      · rfl
    · have h := grassmannianOfSubset_last_mono n V hV
        (a := ⟨(i : ℕ) - V.card - 1, by omega⟩)
        (b := ⟨(i : ℕ) - V.card, by omega⟩) (by
          change (i : ℕ) - V.card - 1 < (i : ℕ) - V.card
          omega)
      convert h using 1 <;> congr 1 <;> apply PNat.eq <;> dsimp <;> omega
  exact not_lt_of_gt hinc hi

/-- Every ordered-subset permutation is Grassmannian. -/
theorem isGrassmannian_grassmannianOfSubset (n : ℕ) (V : Finset ℕ+)
    (hV : V ⊆ positions n) : IsGrassmannian (grassmannianOfSubset n V hV) := by
  rw [IsGrassmannian, Finset.card_le_one]
  intro i hi j hj
  apply PNat.eq
  exact (grassmannianOfSubset_descent_eq n V hV i ((mem_descentSet _ i).mp hi)).trans
    (grassmannianOfSubset_descent_eq n V hV j ((mem_descentSet _ j).mp hj)).symm

/-- The ordered-subset permutation belongs to its ambient Grassmannian family. -/
theorem grassmannianOfSubset_mem_grass (n : ℕ) (V : Finset ℕ+)
    (hV : V ⊆ positions n) : grassmannianOfSubset n V hV ∈ grassmannian n :=
  (mem_grassmannian n _).mpr ⟨isSupported_grassmannianOfSubset n V hV,
    isGrassmannian_grassmannianOfSubset n V hV⟩

/-- A nonidentity ordered-subset permutation descends exactly at its block boundary. -/
theorem grassmannianOfSubset_descent_iff (n : ℕ) (V : Finset ℕ+)
    (hV : V ⊆ positions n) (hw : grassmannianOfSubset n V hV ≠ 1) (i : ℕ+) :
    HasDescent (grassmannianOfSubset n V hV) i ↔ (i : ℕ) = V.card := by
  refine ⟨grassmannianOfSubset_descent_eq n V hV i, ?_⟩
  intro hi
  obtain ⟨j, hj⟩ := exists_descent_of_ne_one (grassmannianOfSubset n V hV) hw
  have hij : i = j := PNat.eq (hi.trans (grassmannianOfSubset_descent_eq n V hV j hj).symm)
  exact hij.symm ▸ hj

end FinitaryPerm
