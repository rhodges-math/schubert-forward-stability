import SchubertForwardStability.Permutations.Classes.Tags.TagCounts
import Mathlib.Data.List.OfFn

/-! # Lists of valid continuation symbols

The recursive local validity condition for a list is equivalent to the indexed
suffix condition. Its finite support is the image of the corresponding vectors.
-/

namespace FinitaryPerm

open scoped Classical

/-- A list is locally valid when each continuation follows a present boundary state. -/
def ValidTagList : Bool → List BlockTag → Prop
  | _, [] => True
  | present, a :: T => (a = .cont → present = true) ∧
      ValidTagList (decide (a ≠ .zero)) T

/-- Recursive list validity agrees with indexed suffix validity. -/
theorem validTagList_ofFn {m : ℕ} (present : Bool) (T : Fin m → BlockTag) :
    ValidTagList present (List.ofFn T) ↔ ValidTagSuffix present T := by
  induction m generalizing present with
  | zero =>
    simp only [List.ofFn_zero, ValidTagList]
    constructor
    · intro _ i
      exact Fin.elim0 i
    · intro _
      trivial
  | succ m ih =>
    rw [← Fin.cons_self_tail T, List.ofFn_cons, ValidTagList, validTagSuffix_cons]
    exact and_congr Iff.rfl (ih _ _)

/-- The finite set of locally valid lists of a prescribed length and boundary state. -/
noncomputable def tagSuffixLists (m : ℕ) (present : Bool) : Finset (List BlockTag) :=
  (Finset.univ.filter (ValidTagSuffix (m := m) present)).image List.ofFn

/-- Membership in the list support is exactly the length and recursive validity condition. -/
theorem mem_tagSuffixLists {m : ℕ} (present : Bool) (T : List BlockTag) :
    T ∈ tagSuffixLists m present ↔ T.length = m ∧ ValidTagList present T := by
  constructor
  · intro h
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp h
    exact ⟨List.length_ofFn, (validTagList_ofFn present Q).mpr
      (Finset.mem_filter.mp hQ).2⟩
  · rintro ⟨hT, hv⟩
    subst m
    apply Finset.mem_image.mpr
    refine ⟨T.get, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, List.ofFn_get T⟩
    apply (validTagList_ofFn present T.get).mp
    simpa only [List.ofFn_get] using hv

/-- The finite list support has the suffix completion count as cardinality. -/
theorem card_tagSuffixLists (m : ℕ) (present : Bool) :
    (tagSuffixLists m present).card = extensionCount m present := by
  exact Finset.card_image_iff.mpr List.ofFn_injective.injOn

/-- The absent-state list support is precisely the list image of the valid tag vectors. -/
theorem tagSuffixLists_false (m : ℕ) :
    tagSuffixLists m false = (tagWords m).image List.ofFn := rfl

/-- The all-zero suffix witnesses that both boundary-state list supports are nonempty. -/
theorem tagSuffixLists_nonempty (m : ℕ) (present : Bool) :
    (tagSuffixLists m present).Nonempty := by
  rw [← Finset.card_pos, card_tagSuffixLists]
  rw [extensionCount, Finset.card_pos]
  refine ⟨fun _ => .zero, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro i hi
  cases hi

end FinitaryPerm
