import SchubertForwardStability.Permutations.Classes.PositiveEvaluation
import SchubertForwardStability.Permutations.Classes.Boolean
import Mathlib.Algebra.Group.End
import Mathlib.Data.Finset.Card

/-! # Generator support of Boolean reduced expressions

Insertion endomorphisms satisfy the adjacent relations. Their evaluation extracts
the finite support of a word, so support is constant across reduced expressions.
-/

namespace FinitaryPerm

open Schubert.FinPermutation

private def insertGenerator (i : ℕ+) : Function.End (Finset ℕ+) := insert i

private theorem insertGenerator_relations (n : ℕ) :
    SatisfiesAdjacentRelations
      (fun a : AdjacentPosition n => insertGenerator (adjacentLetter a)) := by
  constructor
  · intro a b _
    funext s
    change insert (adjacentLetter a)
      (insert (adjacentLetter b) (insert (adjacentLetter a) s)) =
      insert (adjacentLetter b)
        (insert (adjacentLetter a) (insert (adjacentLetter b) s))
    simp [Finset.insert_comm]
  · intro a b _
    funext s
    change insert (adjacentLetter a) (insert (adjacentLetter b) s) =
      insert (adjacentLetter b) (insert (adjacentLetter a) s)
    exact Finset.insert_comm _ _ _

private theorem insertGenerator_prod (word : List ℕ+) :
    (word.map insertGenerator).prod ∅ = word.toFinset := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    change insert i ((word.map insertGenerator).prod ∅) = (i :: word).toFinset
    rw [ih, List.toFinset_cons]

/-- Two reduced expressions of the same permutation contain the same positive generators. -/
theorem reducedWord_toFinset_eq (w : FinitaryPerm ℕ+) (u v : List ℕ+)
    (hu : IsReducedWord w u) (hv : IsReducedWord w v) : u.toFinset = v.toFinset := by
  have h := positiveReduced_eval_eq insertGenerator insertGenerator_relations w u v hu hv
  have he := congrArg (fun f : Function.End (Finset ℕ+) => f ∅) h
  simpa only [insertGenerator_prod] using he

/-- Every reduced expression of a Boolean permutation has distinct generators. -/
theorem IsBoolean.reducedWord_nodup {w : FinitaryPerm ℕ+} (hw : IsBoolean w)
    {word : List ℕ+} (hword : IsReducedWord w word) : word.Nodup := by
  obtain ⟨u, hu, hnu⟩ := hw
  apply (Multiset.toFinset_card_eq_card_iff_nodup (m := (word : Multiset ℕ+))).mp
  change word.toFinset.card = word.length
  rw [reducedWord_toFinset_eq w word u hword hu, List.toFinset_card_of_nodup hnu]
  exact hu.2.trans hword.2.symm

/-- The lexicographically selected reduced expression of a Boolean permutation is distinct. -/
theorem IsBoolean.lexFirst_nodup {w : FinitaryPerm ℕ+} (hw : IsBoolean w) :
    w.lexFirstReducedWord.Nodup := hw.reducedWord_nodup (isReducedWordIn_lexFirst w).1

end FinitaryPerm
