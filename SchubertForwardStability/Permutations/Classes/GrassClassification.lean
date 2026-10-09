import SchubertForwardStability.Permutations.Classes.GrassEncoding
import Mathlib.Order.Fin.Basic

/-! # Classification by increasing subset blocks

A nonidentity Grassmannian permutation has a unique descent. Its values before
that descent form the selected subset, and both blocks are the unique increasing
enumerations of the selected values and their complement.

## Main results

* `IsGrassmannian.descent_unique`: any two descents coincide.
* `strictMono_block_of_no_descent`: consecutive blocks without descents are increasing.
* `exists_grassmannianOfSubset`: every ambient Grassmannian has a subset encoding.

## Implementation notes

The identity uses the empty selected subset. Nonidentity encodings recover their
boundary from the unique descent on positive positions.
-/

namespace FinitaryPerm

open scoped Classical

/-- Any two descents of a Grassmannian permutation coincide. -/
theorem IsGrassmannian.descent_unique {w : FinitaryPerm ℕ+} (hw : IsGrassmannian w)
    {i j : ℕ+} (hi : HasDescent w i) (hj : HasDescent w j) : i = j :=
  Finset.card_le_one.mp hw i ((mem_descentSet w i).mpr hi)
    j ((mem_descentSet w j).mpr hj)

/-- A consecutive block without an internal descent is strictly increasing. -/
theorem strictMono_block_of_no_descent (w : FinitaryPerm ℕ+) (offset length : ℕ)
    (h : ∀ j : ℕ+, offset < (j : ℕ) → (j : ℕ) < offset + length →
      ¬ HasDescent w j) :
    StrictMono (fun i : Fin length ↦ w ⟨offset + i.val + 1, Nat.zero_lt_succ _⟩) := by
  cases length with
  | zero => intro i; exact Fin.elim0 i
  | succ m =>
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    let j : ℕ+ := ⟨offset + i.val + 1, Nat.zero_lt_succ _⟩
    have hj : ¬ HasDescent w j := h j (by change offset < offset + i.val + 1; omega)
      (by change offset + i.val + 1 < offset + (m + 1); have := i.isLt; omega)
    change w j < w (j + 1)
    apply lt_of_le_of_ne (le_of_not_gt hj)
    intro he
    have he' := congrArg PNat.val (w.injective he)
    change offset + i.val + 1 = offset + i.val + 1 + 1 at he'
    omega

/-- The values before a Grassmannian descent recover its ordered-subset encoding. -/
theorem eq_grassmannianOfSubset_of_descent {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (hg : IsGrassmannian w) {k : ℕ+} (hk : HasDescent w k) :
    ∃ V : Finset ℕ+, ∃ hV : V ⊆ positions n, w = grassmannianOfSubset n V hV := by
  let V := (positions (k : ℕ)).image w
  have hV : V ⊆ positions n := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    exact (mem_positions n _).mpr ((hw.apply_le_iff j).mpr
      (((mem_positions (k : ℕ) j).mp hj).trans (Nat.le_of_lt (hw.descent_lt hk))))
  have hc : V.card = (k : ℕ) := by
    dsimp only [V]
    rw [Finset.card_image_of_injective _ w.injective, card_positions]
  have hsum : V.card + (positions n \ V).card = n := by
    rw [Nat.add_comm, Finset.card_sdiff_add_card_eq_card hV, card_positions]
  have hfirst : (fun i : Fin V.card ↦ w ⟨i.val + 1, Nat.zero_lt_succ _⟩) =
      V.orderEmbOfFin rfl := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      apply Finset.mem_image.mpr
      refine ⟨⟨i.val + 1, Nat.zero_lt_succ _⟩, ?_, rfl⟩
      apply (mem_positions (k : ℕ) _).mpr
      change i.val + 1 ≤ (k : ℕ)
      have := i.isLt
      omega
    · have hm := strictMono_block_of_no_descent w 0 V.card (by
        intro j _ hj hdesc
        have he := congrArg PNat.val (hg.descent_unique hdesc hk)
        change (j : ℕ) = (k : ℕ) at he
        omega)
      simpa only [Nat.zero_add] using hm
  have hlast : (fun i : Fin (positions n \ V).card ↦
      w ⟨V.card + i.val + 1, Nat.zero_lt_succ _⟩) =
      (positions n \ V).orderEmbOfFin rfl := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      apply Finset.mem_sdiff.mpr
      constructor
      · apply (mem_positions n _).mpr
        apply (hw.apply_le_iff _).mpr
        change V.card + i.val + 1 ≤ n
        have := i.isLt
        omega
      · intro hm
        obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hm
        have hj' := (mem_positions (k : ℕ) j).mp hj
        have he' := congrArg PNat.val (w.injective he)
        change (j : ℕ) = V.card + i.val + 1 at he'
        omega
    · apply strictMono_block_of_no_descent w V.card (positions n \ V).card
      intro j hj _ hdesc
      have he := congrArg PNat.val (hg.descent_unique hdesc hk)
      change (j : ℕ) = (k : ℕ) at he
      omega
  refine ⟨V, hV, ?_⟩
  apply ext
  intro j
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
      exact congrFun hfirst i
    · let i : Fin (positions n \ V).card := ⟨(j : ℕ) - V.card - 1, by omega⟩
      have hj : (⟨V.card + i.val + 1, Nat.zero_lt_succ _⟩ : ℕ+) = j := by
        apply PNat.eq
        change V.card + i.val + 1 = (j : ℕ)
        dsimp only [i]
        omega
      rw [← hj, grassmannianOfSubset_apply_last]
      exact congrFun hlast i
  · rw [hw j (lt_of_not_ge hjn),
      isSupported_grassmannianOfSubset n V hV j (lt_of_not_ge hjn)]

/-- Every ambient Grassmannian permutation is an ordered-subset encoding. -/
theorem exists_grassmannianOfSubset {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : w ∈ grassmannian n) :
    ∃ V : Finset ℕ+, ∃ hV : V ⊆ positions n, w = grassmannianOfSubset n V hV := by
  by_cases he : w = 1
  · subst w
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    exact (grassmannianOfSubset_eq_one n ∅ (Finset.empty_subset _)
      (by simp only [Finset.card_empty, positions_zero])).symm
  · obtain ⟨k, hk⟩ := exists_descent_of_ne_one w he
    obtain ⟨hs, hg⟩ := (mem_grassmannian n w).mp hw
    exact eq_grassmannianOfSubset_of_descent hs hg hk

end FinitaryPerm
