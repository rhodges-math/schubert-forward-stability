import SchubertForwardStability.Permutations.Finitary.Finite
import Mathlib.Data.Finset.Sort

/-! # Permutation patterns and standardization

## Main definitions

* `PermutationPattern`: a finite permutation representing a relative order.
* `Contains`: occurrence at strictly increasing positive positions.
* `avoiding`: pattern-avoiding permutations in an initial symmetric group.
* `standardize`: the finite permutation of ranks of distinct values.

## Implementation notes

Pattern positions use `Fin k`; occurrences and ambient permutation values use positive
integers. Occurrences are bounded by the explicit ambient size. Standardization is the
inverse of the increasing enumeration of the value set.
-/

/-- A permutation pattern of size `k` is a permutation of `Fin k`. -/
abbrev PermutationPattern (k : ℕ) := Equiv.Perm (Fin k)

namespace PermutationPattern

open scoped Classical

/-- A pattern occurs if an increasing selection of positions has the same relative values. -/
def Contains {k : ℕ} (n : ℕ) (π : PermutationPattern k) (w : FinitaryPerm ℕ+) : Prop :=
  ∃ f : Fin k → ℕ+, StrictMono f ∧ (∀ i, (f i : ℕ) ≤ n) ∧
    ∀ i j, π i < π j ↔ w (f i) < w (f j)

/-- The pattern-avoiding permutations in the first `n` positive positions. -/
noncomputable def avoiding {k : ℕ} (n : ℕ) (π : PermutationPattern k) :
    Finset (FinitaryPerm ℕ+) :=
  (FinitaryPerm.symmetricGroup n).filter fun w => ¬Contains n π w

/-- Avoidance-family membership combines support containment and non-occurrence. -/
@[simp]
theorem mem_avoiding {k : ℕ} (n : ℕ) (π : PermutationPattern k) (w : FinitaryPerm ℕ+) :
    w ∈ avoiding n π ↔ FinitaryPerm.IsSupported n w ∧ ¬Contains n π w := by
  simp only [avoiding, Finset.mem_filter, FinitaryPerm.mem_symmetricGroup]

/-- A nonempty pattern has no occurrence in an empty initial interval. -/
theorem not_contains_zero {k : ℕ} (hk : 0 < k) (π : PermutationPattern k)
    (w : FinitaryPerm ℕ+) : ¬Contains 0 π w := by
  rintro ⟨f, _, hn, _⟩
  exact (not_le_of_gt (PNat.pos (f ⟨0, hk⟩))) (hn ⟨0, hk⟩)

/-- The permutations avoiding every member of a finite list of patterns. -/
noncomputable def avoidingMany (n : ℕ) (patterns : List (Σ k, PermutationPattern k)) :
    Finset (FinitaryPerm ℕ+) :=
  (FinitaryPerm.symmetricGroup n).filter fun w =>
    ∀ π ∈ patterns, ¬Contains n π.2 w

/-- Membership in multiple avoidance requires support containment and every non-occurrence. -/
@[simp]
theorem mem_avoidingMany (n : ℕ) (patterns : List (Σ k, PermutationPattern k))
    (w : FinitaryPerm ℕ+) : w ∈ avoidingMany n patterns ↔
      FinitaryPerm.IsSupported n w ∧ ∀ π ∈ patterns, ¬Contains n π.2 w := by
  simp only [avoidingMany, Finset.mem_filter, FinitaryPerm.mem_symmetricGroup]

/-- A singleton list of forbidden patterns gives the single-pattern avoidance family. -/
theorem avoidingMany_singleton {k : ℕ} (n : ℕ) (π : PermutationPattern k) :
    avoidingMany n [⟨k, π⟩] = avoiding n π := by
  ext w
  simp only [mem_avoidingMany, mem_avoiding, List.mem_singleton, forall_eq]

/-- With no forbidden patterns, the avoidance family is the whole symmetric group. -/
@[simp]
theorem avoidingMany_nil (n : ℕ) : avoidingMany n [] = FinitaryPerm.symmetricGroup n := by
  ext w
  simp only [mem_avoidingMany, FinitaryPerm.mem_symmetricGroup,
    List.not_mem_nil, false_implies, forall_const, and_true]

private def valueSet {k : ℕ} (f : Fin k → ℕ+) : Finset ℕ+ := Finset.univ.image f

private theorem valueSet_card {k : ℕ} (f : Fin k → ℕ+) (hf : Function.Injective f) :
    (valueSet f).card = k := by
  rw [valueSet, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

private noncomputable def valuesEquiv {k : ℕ} (f : Fin k → ℕ+) (hf : Function.Injective f) :
    Fin k ≃ valueSet f := Equiv.ofBijective
  (fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩) (by
    constructor
    · intro i j h
      exact hf (congrArg Subtype.val h)
    · intro j
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp j.property
      exact ⟨i, Subtype.ext hi⟩)

/-- Replace distinct positive values by their ranks in increasing order. -/
noncomputable def standardize {k : ℕ} (f : Fin k → ℕ+)
    (hf : Function.Injective f) : PermutationPattern k :=
  (valuesEquiv f hf).trans ((valueSet f).orderIsoOfFin (valueSet_card f hf)).symm.toEquiv

/-- Standardization preserves and reflects strict comparison of the selected values. -/
theorem standardize_lt_iff {k : ℕ} (f : Fin k → ℕ+) (hf : Function.Injective f) (i j : Fin k) :
    standardize f hf i < standardize f hf j ↔ f i < f j := by
  change ((valueSet f).orderIsoOfFin (valueSet_card f hf)).symm (valuesEquiv f hf i) <
      ((valueSet f).orderIsoOfFin (valueSet_card f hf)).symm (valuesEquiv f hf j) ↔ _
  exact ((valueSet f).orderIsoOfFin (valueSet_card f hf)).symm.lt_iff_lt

/-- Every increasing selection of positions contains its standardized value pattern. -/
theorem contains_standardize {k : ℕ} (n : ℕ) (w : FinitaryPerm ℕ+) (f : Fin k → ℕ+)
    (hf : StrictMono f) (hn : ∀ i, (f i : ℕ) ≤ n) : Contains n (standardize (fun i => w (f i))
      (w.injective.comp hf.injective)) w :=
  ⟨f, hf, hn, fun i j => standardize_lt_iff _ _ i j⟩

end PermutationPattern
