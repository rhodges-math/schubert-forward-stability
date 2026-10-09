import SchubertForwardStability.Permutations.Finitary.Bounds
import Mathlib.Data.Fintype.Perm
import Lean.Elab.Tactic.Omega

/-! # Finite symmetric groups on positive positions

## Main definitions

* `positiveIndex`: the one-based equivalence from `Fin n` to positive positions at most `n`.
* `finiteEquiv`: finite permutations as finitary permutations fixing the complement.
* `ofFinite`, `toFinite`: extension and restriction along this equivalence.
* `symmetricGroup`: the finite family of permutations supported in an initial interval.

## Implementation notes

The finite group includes its identity at size zero. Positive-index permutations use
Mathlib's subtype extension, which fixes every point outside the initial interval.
-/

namespace FinitaryPerm

open scoped Classical

/-- The increasing one-based equivalence from `Fin n` to positive positions at most `n`. -/
def positiveIndex (n : ℕ) : Fin n ≃ {j : ℕ+ // (j : ℕ) ≤ n} where
  toFun i := ⟨⟨i.val + 1, Nat.zero_lt_succ i.val⟩, by
    change i.val + 1 ≤ n
    omega⟩
  invFun j := ⟨(j.val : ℕ) - 1, by
    exact lt_of_lt_of_le (Nat.sub_lt (PNat.pos j.val) (by decide : 0 < 1)) j.property⟩
  left_inv i := by
    apply Fin.ext
    change i.val + 1 - 1 = i.val
    omega
  right_inv j := by
    apply Subtype.ext
    apply PNat.eq
    change (j.val : ℕ) - 1 + 1 = (j.val : ℕ)
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt (PNat.pos j.val))

/-- The positive position associated with a finite index has value one greater. -/
@[simp]
theorem positiveIndex_val (n : ℕ) (i : Fin n) :
    ((positiveIndex n i).val : ℕ) = i.val + 1 := rfl

/-- The finite index of a positive position is its predecessor. -/
@[simp]
theorem positiveIndex_symm_val (n : ℕ) (j : {j : ℕ+ // (j : ℕ) ≤ n}) :
    ((positiveIndex n).symm j).val = (j.val : ℕ) - 1 := rfl

/-- The finite set of positive positions at most `n`. -/
def positions (n : ℕ) : Finset ℕ+ :=
  Finset.univ.image fun i : Fin n => (positiveIndex n i).val

/-- Membership in the initial positive interval is the upper-bound inequality. -/
@[simp]
theorem mem_positions (n : ℕ) (j : ℕ+) : j ∈ positions n ↔ (j : ℕ) ≤ n := by
  constructor
  · intro h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact (positiveIndex n i).property
  · intro h
    refine Finset.mem_image.mpr ⟨(positiveIndex n).symm ⟨j, h⟩, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val ((positiveIndex n).apply_symm_apply ⟨j, h⟩)

/-- The initial interval at size zero is empty. -/
@[simp]
theorem positions_zero : positions 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  exact (Nat.not_le_of_gt (PNat.pos j)) ((mem_positions 0 j).mp hj)

/-- The initial interval contains exactly `n` positive positions. -/
@[simp]
theorem card_positions (n : ℕ) : (positions n).card = n := by
  rw [positions, Finset.card_image_of_injective]
  · simpa only [Finset.card_univ] using Fintype.card_fin n
  · intro i j h
    exact (positiveIndex n).injective (Subtype.ext h)

private theorem finite_moved_of_bounded (n : ℕ) (w : Equiv.Perm ℕ+)
    (h : ∀ j : ℕ+, n < (j : ℕ) → w j = j) : {j | w j ≠ j}.Finite := by
  apply (positions n).finite_toSet.subset
  intro j hj
  apply (mem_positions n j).mpr
  by_contra hn
  exact hj (h j (lt_of_not_ge hn))

private def boundedFinitaryEquiv (n : ℕ) :
    {w : Equiv.Perm ℕ+ // ∀ j : ℕ+, ¬(j : ℕ) ≤ n → w j = j} ≃
      {w : FinitaryPerm ℕ+ // IsSupported n w} where
  toFun w :=
    ⟨ofPerm w.val (finite_moved_of_bounded n w.val
      (fun j hj => w.property j (not_le_of_gt hj))),
      fun j hj => w.property j (not_le_of_gt hj)⟩
  invFun w := ⟨w.val.val, fun j hj => w.property j (lt_of_not_ge hj)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

/-- The canonical equivalence between finite permutations and supported finitary permutations. -/
def finiteEquiv (n : ℕ) : Equiv.Perm (Fin n) ≃
    {w : FinitaryPerm ℕ+ // IsSupported n w} :=
  ((positiveIndex n).permCongr.trans
    (Equiv.Perm.subtypeEquivSubtypePerm fun j : ℕ+ => (j : ℕ) ≤ n)).trans
    (boundedFinitaryEquiv n)

/-- Extend a finite permutation by the identity on all larger positive positions. -/
def ofFinite (n : ℕ) (w : Equiv.Perm (Fin n)) : FinitaryPerm ℕ+ := (finiteEquiv n w).val

/-- Finite extension is Mathlib's extension of the conjugated subtype permutation. -/
theorem ofFinite_val (n : ℕ) (w : Equiv.Perm (Fin n)) :
    (ofFinite n w).val = Equiv.Perm.ofSubtype ((positiveIndex n).permCongr w) := rfl

/-- A finite extension is supported in its original initial interval. -/
theorem isSupported_ofFinite (n : ℕ) (w : Equiv.Perm (Fin n)) : IsSupported n (ofFinite n w) :=
  (finiteEquiv n w).property

/-- Finite extension fixes all positions larger than its size. -/
theorem ofFinite_apply_above (n : ℕ) (w : Equiv.Perm (Fin n)) (j : ℕ+)
    (hj : n < (j : ℕ)) : ofFinite n w j = j := isSupported_ofFinite n w j hj

/-- Finite extension acts on a one-based position by the original finite permutation. -/
@[simp]
theorem ofFinite_apply_position (n : ℕ) (w : Equiv.Perm (Fin n)) (i : Fin n) :
    ofFinite n w (positiveIndex n i).val = (positiveIndex n (w i)).val := by
  change Equiv.Perm.ofSubtype ((positiveIndex n).permCongr w) (positiveIndex n i).val = _
  rw [Equiv.Perm.ofSubtype_apply_coe, Equiv.permCongr_apply,
    Equiv.symm_apply_apply]

/-- Finite extension is injective. -/
theorem ofFinite_injective (n : ℕ) : Function.Injective (ofFinite n) := by
  intro w v h
  exact (finiteEquiv n).injective (Subtype.ext h)

/-- Extending a finite transposition exchanges the corresponding positive positions. -/
theorem ofFinite_swap (n : ℕ) (a b : Fin n) :
    ofFinite n (Equiv.swap a b) = swap (positiveIndex n a).val (positiveIndex n b).val := by
  have hc : (positiveIndex n).permCongr (Equiv.swap a b) =
      Equiv.swap (positiveIndex n a) (positiveIndex n b) := by
    apply Equiv.ext
    intro j
    rw [Equiv.permCongr_apply]
    have h := (positiveIndex n).injective.map_swap a b ((positiveIndex n).symm j)
    simpa only [Equiv.apply_symm_apply] using h
  apply Subtype.ext
  rw [ofFinite_val, hc, Equiv.Perm.ofSubtype_swap_eq]
  rfl

/-- Restrict a supported finitary permutation to the corresponding finite index type. -/
def toFinite (n : ℕ) (w : FinitaryPerm ℕ+) (h : IsSupported n w) : Equiv.Perm (Fin n) :=
  (finiteEquiv n).symm ⟨w, h⟩

/-- Extending a restriction returns the supported finitary permutation. -/
@[simp]
theorem ofFinite_toFinite (n : ℕ) (w : FinitaryPerm ℕ+) (h : IsSupported n w) :
    ofFinite n (toFinite n w h) = w :=
  congrArg Subtype.val ((finiteEquiv n).apply_symm_apply ⟨w, h⟩)

/-- Restricting an extension returns the finite permutation. -/
@[simp]
theorem toFinite_ofFinite (n : ℕ) (w : Equiv.Perm (Fin n)) :
    toFinite n (ofFinite n w) (isSupported_ofFinite n w) = w :=
  (finiteEquiv n).symm_apply_apply w

/-- Extension preserves the identity permutation. -/
@[simp]
theorem ofFinite_one (n : ℕ) : ofFinite n 1 = 1 := by
  apply ext
  intro j
  by_cases hj : (j : ℕ) ≤ n
  · obtain ⟨i, hi⟩ := (positiveIndex n).surjective ⟨j, hj⟩
    have hv : (positiveIndex n i).val = j := congrArg Subtype.val hi
    rw [← hv, ofFinite_apply_position]
    rfl
  · exact ofFinite_apply_above n 1 j (lt_of_not_ge hj)

/-- Extension preserves multiplication of finite permutations. -/
@[simp]
theorem ofFinite_mul (n : ℕ) (w v : Equiv.Perm (Fin n)) :
    ofFinite n (w * v) = ofFinite n w * ofFinite n v := by
  apply ext
  intro j
  by_cases hj : (j : ℕ) ≤ n
  · obtain ⟨i, hi⟩ := (positiveIndex n).surjective ⟨j, hj⟩
    have hv : (positiveIndex n i).val = j := congrArg Subtype.val hi
    rw [← hv, mul_apply, ofFinite_apply_position, ofFinite_apply_position,
      ofFinite_apply_position]
    rfl
  · rw [ofFinite_apply_above n (w * v) j (lt_of_not_ge hj), mul_apply,
      ofFinite_apply_above n v j (lt_of_not_ge hj),
      ofFinite_apply_above n w j (lt_of_not_ge hj)]

/-- The finite family of all permutations supported in the first `n` positive positions. -/
noncomputable def symmetricGroup (n : ℕ) : Finset (FinitaryPerm ℕ+) :=
  Finset.univ.map ⟨ofFinite n, ofFinite_injective n⟩

/-- Membership in the finite symmetric family is exactly support containment. -/
@[simp]
theorem mem_symmetricGroup (n : ℕ) (w : FinitaryPerm ℕ+) :
    w ∈ symmetricGroup n ↔ IsSupported n w := by
  constructor
  · intro h
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp h
    exact isSupported_ofFinite n v
  · intro h
    exact Finset.mem_map.mpr ⟨toFinite n w h, Finset.mem_univ _, ofFinite_toFinite n w h⟩

/-- The finite symmetric family has factorial cardinality. -/
@[simp]
theorem card_symmetricGroup (n : ℕ) : (symmetricGroup n).card = n.factorial := by
  rw [symmetricGroup, Finset.card_map, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- Identity belongs to every finite symmetric family, including at size zero. -/
theorem one_mem_symmetricGroup (n : ℕ) : (1 : FinitaryPerm ℕ+) ∈ symmetricGroup n :=
  (mem_symmetricGroup n 1).mpr (isSupported_one n)

/-- The size-zero symmetric group consists of identity alone. -/
@[simp]
theorem symmetricGroup_zero : symmetricGroup 0 = {1} := by
  ext w
  simp only [mem_symmetricGroup, isSupported_zero_iff, Finset.mem_singleton]

/-- Increasing the ambient size enlarges the finite symmetric family. -/
theorem symmetricGroup_mono {m n : ℕ} (h : m ≤ n) : symmetricGroup m ⊆ symmetricGroup n := by
  intro w hw
  exact (mem_symmetricGroup n w).mpr (((mem_symmetricGroup m w).mp hw).mono h)

/-- The positive forward-stability bound characterizes finite-group membership. -/
theorem forwardStability_le_iff_mem (w : FinitaryPerm ℕ+) {n : ℕ} (hn : 1 ≤ n) :
    w.forwardStability ≤ n ↔ w ∈ symmetricGroup n :=
  (forwardStability_le_iff w hn).trans (mem_symmetricGroup n w).symm

end FinitaryPerm
