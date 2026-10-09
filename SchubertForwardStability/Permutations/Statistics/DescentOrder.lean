import SchubertForwardStability.Permutations.Statistics.Descents
import SchubertForwardStability.TypeA.Permutations.EssentialBigrassmannian

/-! # Identity and descent existence

Every nonidentity finitary permutation has an adjacent descent. Thus the descent
set is empty exactly for identity, including permutations of empty finite support.
-/

namespace FinitaryPerm

open scoped Classical

/-- Every nonidentity finitary permutation has an adjacent descent. -/
theorem exists_descent_of_ne_one (w : FinitaryPerm ℕ+) (hw : w ≠ 1) :
    ∃ i, HasDescent w i := by
  let n := w.forwardStability
  let p := toFinite n w w.isSupported_forwardStability
  have hp : p ≠ Equiv.refl (Fin n) := by
    intro h
    apply hw
    rw [← ofFinite_toFinite n w w.isSupported_forwardStability]
    change ofFinite n p = 1
    rw [h]
    exact ofFinite_one n
  obtain ⟨i, j, hj, hd⟩ := Schubert.FinPermutation.exists_descent_of_ne_refl p hp
  have happ (a : Fin n) : w (positiveIndex n a).val = (positiveIndex n (p a)).val := by
    have he : ofFinite n p = w := ofFinite_toFinite n w w.isSupported_forwardStability
    simpa only [he] using (ofFinite_apply_position n p a)
  have hnext : (positiveIndex n j).val = (positiveIndex n i).val + 1 := by
    apply PNat.eq
    change j.val + 1 = i.val + 1 + 1
    omega
  refine ⟨(positiveIndex n i).val, ?_⟩
  unfold HasDescent
  rw [← hnext, happ, happ]
  change (p j).val + 1 < (p i).val + 1
  exact Nat.add_lt_add_right hd 1

/-- A finitary permutation has empty descent set exactly when it is identity. -/
@[simp]
theorem descentSet_eq_empty (w : FinitaryPerm ℕ+) : w.descentSet = ∅ ↔ w = 1 := by
  constructor
  · intro h
    by_contra hw
    obtain ⟨i, hi⟩ := exists_descent_of_ne_one w hw
    have hm := (mem_descentSet w i).mpr hi
    rw [h] at hm
    exact Finset.notMem_empty i hm
  · rintro rfl
    exact descentSet_one

end FinitaryPerm
