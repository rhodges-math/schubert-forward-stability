import SchubertForwardStability.Permutations.Classes.DescentDiamonds
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Monoid evaluation of reduced sorting words

## Main definitions

* `SatisfiesAdjacentRelations`: a monoid-valued generator assignment satisfying
  the finite type-A braid and distant-commutation relations.

## Main results

Every such assignment gives the same monoid product on all descending words
sorting a given permutation to identity.

## Implementation notes

The proof is by inversion-length induction using the two descent diamonds.
No cancellation, invertibility or square relation is required in the target monoid.
-/

namespace FinitaryPerm

open Schubert (FinPermutation)
open Schubert.FinPermutation

variable {n : ℕ} {M : Type*} [Monoid M]

/-- A monoid-valued assignment respects the finite adjacent braid and commutation relations. -/
def SatisfiesAdjacentRelations (f : AdjacentPosition n → M) : Prop :=
  (∀ a b, a.right = b.left → f a * f b * f a = f b * f a * f b) ∧
    (∀ a b, Schubert.SeparatedAdjacentPositions a b → f a * f b = f b * f a)

/-- The chosen reduced sorting word is descending at every step. -/
theorem descending_reducedWordToRefl (w : FinPermutation n) :
    IsDescendingWord w (reducedWordToRefl w) := by
  apply isDescendingWord_of_length_eq
  rw [apply_reducedWordToRefl, length_reducedWordToRefl, length_refl, Nat.add_zero]

/-- Concatenation is descending exactly when each portion is descending at its starting point. -/
theorem descendingWord_append (w : FinPermutation n) (left right : List (AdjacentPosition n)) :
    IsDescendingWord w (left ++ right) ↔
      IsDescendingWord w left ∧ IsDescendingWord (applyRightAdjacentWord left w) right := by
  induction left generalizing w with
  | nil => simp only [List.nil_append, IsDescendingWord, applyRightAdjacentWord_nil, true_and]
  | cons a left ih =>
    simp only [List.cons_append, IsDescendingWord, applyRightAdjacentWord_cons, ih, and_assoc]

/-- The only descending word starting at identity is the empty word. -/
theorem descending_identity_word (word : List (AdjacentPosition n))
    (hdesc : IsDescendingWord (Equiv.refl (Fin n)) word) : word = [] := by
  have hlength := length_applyRightAdjacentWord_of_isDescending word _ hdesc
  rw [length_refl] at hlength
  apply List.eq_nil_of_length_eq_zero
  omega

private theorem sorting_eval_of_diamond (f : AdjacentPosition n → M)
    (w : FinPermutation n) (a b : AdjacentPosition n)
    (u v left right : List (AdjacentPosition n))
    (hu : IsDescendingWord w (a :: u)) (hv : IsDescendingWord w (b :: v))
    (hsu : applyRightAdjacentWord (a :: u) w = Equiv.refl (Fin n))
    (hsv : applyRightAdjacentWord (b :: v) w = Equiv.refl (Fin n))
    (hl : IsDescendingWord w (a :: left)) (hr : IsDescendingWord w (b :: right))
    (hend : applyRightAdjacentWord (a :: left) w = applyRightAdjacentWord (b :: right) w)
    (hprod : f a * (left.map f).prod = f b * (right.map f).prod)
    (ih : ∀ g : FinPermutation n, g.length < w.length →
      ∀ x y : List (AdjacentPosition n), IsDescendingWord g x → IsDescendingWord g y →
      applyRightAdjacentWord x g = Equiv.refl (Fin n) →
      applyRightAdjacentWord y g = Equiv.refl (Fin n) → (x.map f).prod = (y.map f).prod) :
    ((a :: u).map f).prod = ((b :: v).map f).prod := by
  let q := applyRightAdjacentWord (a :: left) w
  let z := reducedWordToRefl q
  have hlz : IsDescendingWord (w.rightAdjacentSwap a) (left ++ z) := by
    apply (descendingWord_append _ _ _).mpr
    exact ⟨hl.2, descending_reducedWordToRefl q⟩
  have hrz : IsDescendingWord (w.rightAdjacentSwap b) (right ++ z) := by
    apply (descendingWord_append _ _ _).mpr
    refine ⟨hr.2, ?_⟩
    change IsDescendingWord (applyRightAdjacentWord (b :: right) w) z
    rw [← hend]
    exact descending_reducedWordToRefl q
  have hls : applyRightAdjacentWord (left ++ z) (w.rightAdjacentSwap a) =
      Equiv.refl (Fin n) := by
    rw [applyRightAdjacentWord_append]
    exact apply_reducedWordToRefl q
  have hrs : applyRightAdjacentWord (right ++ z) (w.rightAdjacentSwap b) =
      Equiv.refl (Fin n) := by
    rw [applyRightAdjacentWord_append]
    change applyRightAdjacentWord z (applyRightAdjacentWord (b :: right) w) = _
    rw [← hend]
    exact apply_reducedWordToRefl q
  have hdropa := length_rightAdjacentSwap_of_descent w a hu.1
  have hdropb := length_rightAdjacentSwap_of_descent w b hv.1
  have hau := ih (w.rightAdjacentSwap a) (by omega) u (left ++ z) hu.2 hlz hsu hls
  have hbv := ih (w.rightAdjacentSwap b) (by omega) v (right ++ z) hv.2 hrz hsv hrs
  simp only [List.map_cons, List.prod_cons]
  rw [hau, hbv, List.map_append, List.map_append, List.prod_append, List.prod_append,
    ← mul_assoc, ← mul_assoc, hprod]

/-- All descending words sorting a fixed permutation have the same monoid evaluation. -/
theorem sortingWord_eval_eq (f : AdjacentPosition n → M) (hf : SatisfiesAdjacentRelations f)
    (w : FinPermutation n) :
    ∀ u v : List (AdjacentPosition n), IsDescendingWord w u → IsDescendingWord w v →
      applyRightAdjacentWord u w = Equiv.refl (Fin n) →
      applyRightAdjacentWord v w = Equiv.refl (Fin n) → (u.map f).prod = (v.map f).prod := by
  generalize hm : w.length = m
  induction m using Nat.strong_induction_on generalizing w with
  | h m ih =>
    intro u v hu hv hsu hsv
    have hind (g : FinPermutation n) (hg : g.length < w.length) :=
      ih g.length (by omega) g rfl
    cases u with
    | nil =>
      change w = Equiv.refl (Fin n) at hsu
      rw [hsu] at hv
      have hvnil := descending_identity_word v hv
      subst v
      rfl
    | cons a u =>
      cases v with
      | nil =>
        change w = Equiv.refl (Fin n) at hsv
        rw [hsv] at hu
        have hunil := descending_identity_word (a :: u) hu
        cases hunil
      | cons b v =>
        rcases adjacentPosition_cases a b with heq | hgap | hab | hba
        · subst b
          have hdrop := length_rightAdjacentSwap_of_descent w a hu.1
          simp only [List.map_cons, List.prod_cons]
          rw [hind (w.rightAdjacentSwap a) (by omega) u v hu.2 hv.2 hsu hsv]
        · obtain ⟨hl, hr⟩ := descending_separated w a b hgap ⟨hu.1, hv.1⟩
          apply sorting_eval_of_diamond f w a b u v [b] [a] hu hv hsu hsv hl hr
            (separated_sorting_endpoint w a b hgap) _ hind
          simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
            using hf.2 a b hgap
        · obtain ⟨hl, hr⟩ := descending_braid w a b ⟨hab, hu.1, hv.1⟩
          apply sorting_eval_of_diamond f w a b u v [b, a] [a, b] hu hv hsu hsv hl hr
            (braid_sorting_endpoint w a b hab) _ hind
          simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
            mul_one, mul_assoc] using hf.1 a b hab
        · obtain ⟨hl, hr⟩ := descending_braid w b a ⟨hba, hv.1, hu.1⟩
          symm
          apply sorting_eval_of_diamond f w b a v u [a, b] [b, a] hv hu hsv hsu hl hr
            (braid_sorting_endpoint w b a hba) _ hind
          simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
            mul_one, mul_assoc] using hf.1 b a hba

/-- A word sorts the inverse of its own identity-started product to identity. -/
theorem adjacentWord_sorts_inverse (word : List (AdjacentPosition n)) :
    applyRightAdjacentWord word (applyRightAdjacentWord word (Equiv.refl (Fin n))).symm =
      Equiv.refl (Fin n) := by
  rw [applyRightAdjacentWord_eq_trans]
  exact Equiv.self_trans_symm _

/-- The inversion length of a word's product is at most its number of letters. -/
theorem adjacentWord_length_le (word : List (AdjacentPosition n)) :
    (applyRightAdjacentWord word (Equiv.refl (Fin n))).length ≤ word.length := by
  have hbound := length_le_word_length_add_result word
    (applyRightAdjacentWord word (Equiv.refl (Fin n))).symm
  simpa only [adjacentWord_sorts_inverse, length_refl, Nat.add_zero, length_symm] using hbound

/-- Reduced words with the same finite permutation product have the same monoid evaluation. -/
theorem reducedWord_eval_eq (f : AdjacentPosition n → M) (hf : SatisfiesAdjacentRelations f)
    (w : FinPermutation n) (u v : List (AdjacentPosition n))
    (hsu : applyRightAdjacentWord u (Equiv.refl (Fin n)) = w)
    (hsv : applyRightAdjacentWord v (Equiv.refl (Fin n)) = w)
    (hlu : u.length = w.length) (hlv : v.length = w.length) :
    (u.map f).prod = (v.map f).prod := by
  have hu : applyRightAdjacentWord u w.symm = Equiv.refl (Fin n) := by
    rw [applyRightAdjacentWord_eq_trans, hsu]
    exact Equiv.self_trans_symm w
  have hv : applyRightAdjacentWord v w.symm = Equiv.refl (Fin n) := by
    rw [applyRightAdjacentWord_eq_trans, hsv]
    exact Equiv.self_trans_symm w
  apply sortingWord_eval_eq f hf w.symm u v _ _ hu hv
  · apply isDescendingWord_of_length_eq
    rw [hu, length_refl, Nat.add_zero, length_symm, hlu]
  · apply isDescendingWord_of_length_eq
    rw [hv, length_refl, Nat.add_zero, length_symm, hlv]

end FinitaryPerm
