import SchubertForwardStability.Permutations.Statistics.Descents
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Grassmannian permutations

## Main definitions

* `IsGrassmannian`: at most one adjacent descent.
* `grassmannian`: Grassmannian permutations in an initial symmetric group.
* `grassmannianOfSubset`: the increasing selected values followed by the increasing complement.

## Implementation notes

Identity is included in the Grassmannian family. Subsets consist of positive values
in the chosen initial interval; Mathlib's increasing finite-set enumeration orders each block.
-/

namespace FinitaryPerm

open scoped Classical

/-- A permutation is Grassmannian if it has at most one descent. -/
noncomputable def IsGrassmannian (w : FinitaryPerm ℕ+) : Prop := w.descentSet.card ≤ 1

/-- Grassmannian permutations supported in the first `n` positive positions. -/
noncomputable def grassmannian (n : ℕ) : Finset (FinitaryPerm ℕ+) :=
  (symmetricGroup n).filter IsGrassmannian

/-- Grassmannian-family membership combines support containment and at most one descent. -/
@[simp]
theorem mem_grassmannian (n : ℕ) (w : FinitaryPerm ℕ+) :
    w ∈ grassmannian n ↔ IsSupported n w ∧ IsGrassmannian w := by
  simp only [grassmannian, Finset.mem_filter, mem_symmetricGroup]

/-- Identity is Grassmannian. -/
theorem isGrassmannian_one : IsGrassmannian (1 : FinitaryPerm ℕ+) := by
  rw [IsGrassmannian, descentSet_one, Finset.card_empty]
  exact Nat.zero_le 1

/-- Every ambient Grassmannian family contains identity, including at size zero. -/
theorem one_mem_grassmannian (n : ℕ) : (1 : FinitaryPerm ℕ+) ∈ grassmannian n :=
  (mem_grassmannian n 1).mpr ⟨isSupported_one n, isGrassmannian_one⟩

private def subsetUnionEquiv (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) :
    ↥V ⊕ ↥(positions n \ V) ≃ {j : ℕ+ // (j : ℕ) ≤ n} where
  toFun
    | Sum.inl v => ⟨v.val, (mem_positions n v.val).mp (hV v.property)⟩
    | Sum.inr v => ⟨v.val, (mem_positions n v.val).mp (Finset.mem_sdiff.mp v.property).1⟩
  invFun j := if h : j.val ∈ V then Sum.inl ⟨j.val, h⟩ else
    Sum.inr ⟨j.val, Finset.mem_sdiff.mpr ⟨(mem_positions n j.val).mpr j.property, h⟩⟩
  left_inv v := by
    cases v with
    | inl v => simp only [dite_eq_left v.property]
    | inr v => simp only [dite_eq_right (Finset.mem_sdiff.mp v.property).2]
  right_inv j := by
    by_cases h : j.val ∈ V
    · simp only [dite_eq_left h]
    · simp only [dite_eq_right h]

private theorem subsetBlocks_card (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) :
    V.card + (positions n \ V).card = n := by
  rw [Nat.add_comm, Finset.card_sdiff_add_card_eq_card hV, card_positions]

private def subsetBlocksPerm (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) :
    Equiv.Perm (Fin n) :=
  (((finCongr (subsetBlocks_card n V hV).symm).trans finSumFinEquiv.symm).trans
    (Equiv.sumCongr (V.orderIsoOfFin rfl).toEquiv
      ((positions n \ V).orderIsoOfFin rfl).toEquiv)).trans
    ((subsetUnionEquiv n V hV).trans (positiveIndex n).symm)

/-- The permutation listing `V` increasingly, followed by its increasing
initial-interval complement. -/
noncomputable def grassmannianOfSubset (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) :
    FinitaryPerm ℕ+ := ofFinite n (subsetBlocksPerm n V hV)

/-- A two-block subset permutation fixes all positions beyond its ambient size. -/
theorem isSupported_grassmannianOfSubset (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) :
    IsSupported n (grassmannianOfSubset n V hV) := isSupported_ofFinite n _

/-- The subset permutation belongs to its ambient symmetric group. -/
theorem grassmannianOfSubset_mem (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) :
    grassmannianOfSubset n V hV ∈ symmetricGroup n :=
  (mem_symmetricGroup n _).mpr (isSupported_grassmannianOfSubset n V hV)

/-- The first block of a subset permutation is the increasing enumeration of the subset. -/
theorem grassmannianOfSubset_apply_first (n : ℕ) (V : Finset ℕ+)
    (hV : V ⊆ positions n) (i : Fin V.card) :
    grassmannianOfSubset n V hV ⟨i.val + 1, Nat.zero_lt_succ _⟩ =
      (V.orderIsoOfFin rfl i).val := by
  let a : Fin n := Fin.cast (subsetBlocks_card n V hV)
    (Fin.castAdd (positions n \ V).card i)
  have ha : finCongr (subsetBlocks_card n V hV).symm a =
      Fin.castAdd (positions n \ V).card i := rfl
  change ofFinite n (subsetBlocksPerm n V hV) (positiveIndex n a).val = _
  rw [ofFinite_apply_position]
  change ((positiveIndex n) ((positiveIndex n).symm
    ((subsetUnionEquiv n V hV) ((Equiv.sumCongr (V.orderIsoOfFin rfl).toEquiv
      ((positions n \ V).orderIsoOfFin rfl).toEquiv)
        (finSumFinEquiv.symm (finCongr (subsetBlocks_card n V hV).symm a)))))).val = _
  rw [ha, finSumFinEquiv_symm_apply_castAdd, Equiv.apply_symm_apply]
  rfl

/-- The second block of a subset permutation is the increasing enumeration of its complement. -/
theorem grassmannianOfSubset_apply_last (n : ℕ) (V : Finset ℕ+)
    (hV : V ⊆ positions n) (i : Fin (positions n \ V).card) :
    grassmannianOfSubset n V hV ⟨V.card + i.val + 1, Nat.zero_lt_succ _⟩ =
      ((positions n \ V).orderIsoOfFin rfl i).val := by
  let a : Fin n := Fin.cast (subsetBlocks_card n V hV) (Fin.natAdd V.card i)
  have ha : finCongr (subsetBlocks_card n V hV).symm a = Fin.natAdd V.card i := rfl
  change ofFinite n (subsetBlocksPerm n V hV) (positiveIndex n a).val = _
  rw [ofFinite_apply_position]
  change ((positiveIndex n) ((positiveIndex n).symm
    ((subsetUnionEquiv n V hV) ((Equiv.sumCongr (V.orderIsoOfFin rfl).toEquiv
      ((positions n \ V).orderIsoOfFin rfl).toEquiv)
        (finSumFinEquiv.symm (finCongr (subsetBlocks_card n V hV).symm a)))))).val = _
  rw [ha, finSumFinEquiv_symm_apply_natAdd, Equiv.apply_symm_apply]
  rfl

end FinitaryPerm
