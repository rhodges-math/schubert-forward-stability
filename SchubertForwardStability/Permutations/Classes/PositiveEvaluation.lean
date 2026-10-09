import SchubertForwardStability.Permutations.Classes.FiniteWords
import SchubertForwardStability.Permutations.Classes.SortingEvaluation
import Mathlib.Data.Finset.Lattice.Fold

/-! # Monoid evaluation of positive-index reduced words

The finite adjacent-word evaluation theorem transports to positive words using a
common finite alphabet bound. All target relations are explicit monoid relations.
-/

namespace FinitaryPerm

open Schubert.FinPermutation

/-- Bounded reduced expressions have equal evaluations under the finite adjacent relations. -/
theorem boundedReduced_eval_eq {n : ℕ} {M : Type*} [Monoid M] (f : ℕ+ → M)
    (hf : SatisfiesAdjacentRelations (fun a : AdjacentPosition n => f (adjacentLetter a)))
    (w : FinitaryPerm ℕ+) (u v : List ℕ+) (hu : IsReducedWordIn n w u)
    (hv : IsReducedWordIn n w v) : (u.map f).prod = (v.map f).prod := by
  obtain ⟨U, hU⟩ := exists_finiteAdjacentWord u hu.2
  obtain ⟨V, hV⟩ := exists_finiteAdjacentWord v hv.2
  let g := applyRightAdjacentWord U (Equiv.refl (Fin n))
  have hgu : ofFinite n g = w := by
    rw [ofFinite_wordProduct, hU, hu.1.1]
  have hgv : ofFinite n (applyRightAdjacentWord V (Equiv.refl (Fin n))) = w := by
    rw [ofFinite_wordProduct, hV, hv.1.1]
  have hg : applyRightAdjacentWord V (Equiv.refl (Fin n)) = g :=
    ofFinite_injective n (hgv.trans hgu.symm)
  have hlen : w.length = g.length := by simpa only [hgu] using length_ofFinite n g
  have hlu : U.length = g.length := by
    calc
      U.length = (U.map adjacentLetter).length := (List.length_map adjacentLetter).symm
      _ = u.length := congrArg List.length hU
      _ = w.length := hu.1.2
      _ = g.length := hlen
  have hlv : V.length = g.length := by
    calc
      V.length = (V.map adjacentLetter).length := (List.length_map adjacentLetter).symm
      _ = v.length := congrArg List.length hV
      _ = w.length := hv.1.2
      _ = g.length := hlen
  have h := reducedWord_eval_eq (fun a => f (adjacentLetter a)) hf g U V rfl hg hlu hlv
  rw [← hU, ← hV]
  simpa only [List.map_map, Function.comp_def] using h

/-- Positive reduced expressions have equal evaluations when every finite assignment obeys
the adjacent braid and separated-commutation relations. -/
theorem positiveReduced_eval_eq {M : Type*} [Monoid M] (f : ℕ+ → M)
    (hf : ∀ n : ℕ, SatisfiesAdjacentRelations (fun a : AdjacentPosition n => f (adjacentLetter a)))
    (w : FinitaryPerm ℕ+) (u v : List ℕ+) (hu : IsReducedWord w u) (hv : IsReducedWord w v) :
    (u.map f).prod = (v.map f).prod := by
  classical
  let s := u.toFinset ∪ v.toFinset
  let n := s.sup PNat.val + 1
  have hUB : ∀ i ∈ u, (i : ℕ) < n := by
    intro i hi
    have hmem : i ∈ s := Finset.mem_union.mpr (Or.inl (List.mem_toFinset.mpr hi))
    exact Nat.lt_succ_of_le (Finset.le_sup hmem)
  have hVB : ∀ i ∈ v, (i : ℕ) < n := by
    intro i hi
    have hmem : i ∈ s := Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr hi))
    exact Nat.lt_succ_of_le (Finset.le_sup hmem)
  exact boundedReduced_eval_eq f (hf n) w u v ⟨hu, hUB⟩ ⟨hv, hVB⟩

end FinitaryPerm
