import SchubertForwardStability.Permutations.Random.Tags.TagPartial
import Mathlib.Tactic

/-! # Conditional suffix events under the uniform tag law

A fixed valid prefix leaves the uniform law on suffixes compatible with its final
presence state. The proof is a bijection of completion events and includes
empty suffixes. Prefix lengths are positive; the empty prefix corresponds to the
external absent state.
-/

open MeasureTheory ProbabilityTheory FinitaryPerm
open scoped Classical

namespace RecordStability

/-- Completions of a nonempty valid tag prefix with a prescribed suffix event are
in bijection with the compatible suffixes lying in that event. -/
noncomputable def tagCompletionEventEquiv {t m : ℕ} (P : Fin t → BlockTag)
    (ht : 0 < t) (hP : IsTagWord P) (B : Set (Fin m → BlockTag)) :
    {T : Fin (t + m) → BlockTag //
      T ∈ (tagExtensions P m).filter fun T => (fun j => T (j.natAdd t)) ∈ B} ≃
    {Q : Fin m → BlockTag // ValidTagSuffix (tagPrefixPresent P ht) Q ∧ Q ∈ B} where
  toFun T := by
    refine ⟨fun j => T.val (j.natAdd t), ?_, (Finset.mem_filter.mp T.property).2⟩
    exact (tagCompletionEquiv (m := m) P ht hP
      ⟨T.val, (Finset.mem_filter.mp T.property).1⟩).property
  invFun Q := by
    refine ⟨Fin.append P Q.val, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr
        ⟨(mem_tagWords _).mpr ((validTagSuffix_append false P Q.val ht).mpr
          ⟨hP, Q.property.1⟩), fun i => Fin.append_left P Q.val i⟩
    · have he : (fun j : Fin m => Fin.append P Q.val (j.natAdd t)) = Q.val :=
        funext fun j => Fin.append_right P Q.val j
      rw [he]
      exact Q.property.2
  left_inv T := by
    apply Subtype.ext
    funext r
    change Fin.append P (fun j => T.val (j.natAdd t)) r = T.val r
    refine Fin.addCases (fun i => ?_) (fun j => ?_) r
    · rw [Fin.append_left]
      exact ((Finset.mem_filter.mp
        (Finset.mem_filter.mp T.property).1).2 i).symm
    · exact Fin.append_right _ _ j
  right_inv Q := by
    apply Subtype.ext
    funext j
    change Fin.append P Q.val (j.natAdd t) = Q.val j
    exact Fin.append_right _ _ j

/-- The number of prefix completions satisfying a suffix event depends only on
the final prefix presence state and on the compatible suffix event. -/
theorem card_tagCompletionEvent {t m : ℕ} (P : Fin t → BlockTag) (ht : 0 < t)
    (hP : IsTagWord P) (B : Set (Fin m → BlockTag)) :
    ((tagExtensions P m).filter fun T => (fun j => T (j.natAdd t)) ∈ B).card =
      (Finset.univ.filter fun Q : Fin m → BlockTag =>
        ValidTagSuffix (tagPrefixPresent P ht) Q ∧ Q ∈ B).card := by
  rw [← Fintype.card_coe, Fintype.card_congr (tagCompletionEventEquiv P ht hP B),
    Fintype.card_subtype]

/-- A fixed valid prefix and a suffix event have uniform-tag probability equal
to their compatible suffix count divided by the total tag-word count. -/
theorem tagLaw_prefix_event {t m : ℕ} (P : Fin t → BlockTag) (ht : 0 < t)
    (hP : IsTagWord P) (B : Set (Fin m → BlockTag)) :
    (tagLaw (t + m)).real {T | (∀ i : Fin t, T (i.castAdd m) = P i) ∧
      (fun j : Fin m => T (j.natAdd t)) ∈ B} =
      ((Finset.univ.filter fun Q : Fin m → BlockTag =>
        ValidTagSuffix (tagPrefixPresent P ht) Q ∧ Q ∈ B).card : ℝ) /
          (tagWords (t + m)).card := by
  rw [tagLaw_real_set]
  simp only [Set.mem_ofPred_eq]
  have he : (tagWords (t + m)).filter (fun T =>
      (∀ i : Fin t, T (i.castAdd m) = P i) ∧ (fun j : Fin m => T (j.natAdd t)) ∈ B) =
      (tagExtensions P m).filter fun T => (fun j => T (j.natAdd t)) ∈ B := by
    ext T
    simp only [tagExtensions, Finset.mem_filter]
    tauto
  rw [he, card_tagCompletionEvent P ht hP B]

/-- A nonempty valid prefix cylinder has probability given by its final-state
completion count divided by the total tag-word count. -/
theorem tagLaw_prefix_mass {t m : ℕ} (P : Fin t → BlockTag) (ht : 0 < t)
    (hP : IsTagWord P) :
    (tagLaw (t + m)).real {T | ∀ i : Fin t, T (i.castAdd m) = P i} =
      (extensionCount m (tagPrefixPresent P ht) : ℝ) / (tagWords (t + m)).card := by
  rw [tagLaw_real_set]
  simp only [Set.mem_ofPred_eq]
  change ((tagExtensions P m).card : ℝ) / _ = _
  rw [card_tagExtensions P ht hP]

/-- Conditioning a uniform tag word on a fixed nonempty valid prefix produces
the uniform compatible suffix law. The conditioning event is strictly positive. -/
theorem tagLaw_prefix_conditional {t m : ℕ} (P : Fin t → BlockTag) (ht : 0 < t)
    (hP : IsTagWord P) (B : Set (Fin m → BlockTag)) :
    0 < (tagLaw (t + m)).real {T | ∀ i : Fin t, T (i.castAdd m) = P i} ∧
      (tagLaw (t + m)).real {T | (∀ i : Fin t, T (i.castAdd m) = P i) ∧
        (fun j : Fin m => T (j.natAdd t)) ∈ B} /
        (tagLaw (t + m)).real {T | ∀ i : Fin t, T (i.castAdd m) = P i} =
      ((Finset.univ.filter fun Q : Fin m → BlockTag =>
        ValidTagSuffix (tagPrefixPresent P ht) Q ∧ Q ∈ B).card : ℝ) /
          extensionCount m (tagPrefixPresent P ht) := by
  rw [tagLaw_prefix_mass P ht hP, tagLaw_prefix_event P ht hP B]
  have hU : 0 < (extensionCount m (tagPrefixPresent P ht) : ℝ) := by
    exact_mod_cast extensionCount_pos m _
  have hW : 0 < ((tagWords (t + m)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (tagWords_nonempty _)
  refine ⟨div_pos hU hW, ?_⟩
  field_simp

end RecordStability
