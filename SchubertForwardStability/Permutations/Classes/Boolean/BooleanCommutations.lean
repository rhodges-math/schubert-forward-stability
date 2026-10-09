import SchubertForwardStability.Permutations.Classes.Boolean.BooleanLex
import SchubertForwardStability.Permutations.Classes.SortingEvaluation
import SchubertForwardStability.Permutations.Classes.FiniteWords

/-! # Commutation connectivity of Boolean reduced expressions

Complete sorting words of a Boolean permutation have distinct positive generators.
Consecutive descent diamonds would produce a repeated generator, so the sorting
induction uses separated diamonds only and yields a chain of commutation moves.

## References

Bridget Eileen Tenner, Pattern avoidance and the Bruhat order, Journal of
Combinatorial Theory, Series A 114(5), 888-905 (2007).
-/

namespace FinitaryPerm

open Schubert (FinPermutation)
open Schubert.FinPermutation

variable {n : ℕ}

private abbrev CommChain (a b : List ℕ+) := Relation.ReflTransGen WordCommutation a b

private theorem commutation_symm {a b : List ℕ+} (h : WordCommutation a b) :
    WordCommutation b a := by
  obtain ⟨pre, suf, i, j, ha, hb, hgap⟩ := h
  exact ⟨pre, suf, j, i, hb, ha, hgap.elim Or.inr Or.inl⟩

private theorem commChain_symm {a b : List ℕ+} (h : CommChain a b) : CommChain b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (commutation_symm hbc)).trans ih

private theorem commutation_prefix (p : List ℕ+) {a b : List ℕ+}
    (h : WordCommutation a b) : WordCommutation (p ++ a) (p ++ b) := by
  obtain ⟨pre, suf, i, j, ha, hb, hgap⟩ := h
  exact ⟨p ++ pre, suf, i, j, by simp only [ha, List.append_assoc],
    by simp only [hb, List.append_assoc], hgap⟩

private theorem commChain_prefix (p : List ℕ+) {a b : List ℕ+} (h : CommChain a b) :
    CommChain (p ++ a) (p ++ b) := h.lift (fun a => p ++ a) (fun _ _ h => commutation_prefix p h)

private def AllSortingDistinct (g : FinPermutation n) : Prop :=
  ∀ word : List (AdjacentPosition n), IsDescendingWord g word →
    applyRightAdjacentWord word g = Equiv.refl (Fin n) → (word.map adjacentLetter).Nodup

private theorem sortingDistinct_step (g : FinPermutation n) (a : AdjacentPosition n)
    (ha : g.HasDescent a.left) (hN : AllSortingDistinct g) :
    AllSortingDistinct (g.rightAdjacentSwap a) := by
  intro word hw hs
  have h := hN (a :: word) ⟨ha, hw⟩ hs
  exact (List.nodup_cons.mp h).2

private theorem sortingDistinct_no_braid (g : FinPermutation n) (a b : AdjacentPosition n)
    (hN : AllSortingDistinct g) (hab : a.right = b.left)
    (ha : g.HasDescent a.left) (hb : g.HasDescent b.left) : False := by
  let q := applyRightAdjacentWord [a, b, a] g
  let z := reducedWordToRefl q
  have hd : IsDescendingWord g ([a, b, a] ++ z) := by
    apply (descendingWord_append g _ _).mpr
    exact ⟨(descending_braid g a b ⟨hab, ha, hb⟩).1, descending_reducedWordToRefl q⟩
  have hs : applyRightAdjacentWord ([a, b, a] ++ z) g = Equiv.refl (Fin n) := by
    rw [applyRightAdjacentWord_append]
    exact apply_reducedWordToRefl q
  have hn := hN _ hd hs
  simp only [List.map_cons, List.cons_append, List.nil_append] at hn
  exact (List.nodup_cons.mp hn).1 (by simp)

private theorem separatedLetters (a b : AdjacentPosition n)
    (hgap : Schubert.SeparatedAdjacentPositions a b) :
    adjacentLetter a + 1 < adjacentLetter b ∨ adjacentLetter b + 1 < adjacentLetter a := by
  rcases hgap with hgap | hgap
  · left
    have hr := a.right_val
    change a.left.val + 1 + 1 < b.left.val + 1
    omega
  · right
    have hr := b.right_val
    change b.left.val + 1 + 1 < a.left.val + 1
    omega

private theorem sorting_comm_of_gap (g : FinPermutation n) (a b : AdjacentPosition n)
    (hN : AllSortingDistinct g) (hgap : Schubert.SeparatedAdjacentPositions a b)
    (u v : List (AdjacentPosition n))
    (hu : IsDescendingWord g (a :: u)) (hv : IsDescendingWord g (b :: v))
    (hsu : applyRightAdjacentWord (a :: u) g = Equiv.refl (Fin n))
    (hsv : applyRightAdjacentWord (b :: v) g = Equiv.refl (Fin n))
    (ih : ∀ q : FinPermutation n, q.length < g.length → AllSortingDistinct q →
      ∀ x y : List (AdjacentPosition n), IsDescendingWord q x → IsDescendingWord q y →
      applyRightAdjacentWord x q = Equiv.refl (Fin n) →
      applyRightAdjacentWord y q = Equiv.refl (Fin n) →
        CommChain (x.map adjacentLetter) (y.map adjacentLetter)) :
    CommChain ((a :: u).map adjacentLetter) ((b :: v).map adjacentLetter) := by
  obtain ⟨hl, hr⟩ := descending_separated g a b hgap ⟨hu.1, hv.1⟩
  let q := applyRightAdjacentWord [a, b] g
  let z := reducedWordToRefl q
  have hend := separated_sorting_endpoint g a b hgap
  have hlz : IsDescendingWord (g.rightAdjacentSwap a) (b :: z) := by
    exact ⟨hl.2.1, descending_reducedWordToRefl q⟩
  have hrz : IsDescendingWord (g.rightAdjacentSwap b) (a :: z) := by
    refine ⟨hr.2.1, ?_⟩
    change IsDescendingWord (applyRightAdjacentWord [b, a] g) z
    rw [← hend]
    exact descending_reducedWordToRefl q
  have hls : applyRightAdjacentWord (b :: z) (g.rightAdjacentSwap a) =
      Equiv.refl (Fin n) := apply_reducedWordToRefl q
  have hrs : applyRightAdjacentWord (a :: z) (g.rightAdjacentSwap b) =
      Equiv.refl (Fin n) := by
    change applyRightAdjacentWord z (applyRightAdjacentWord [b, a] g) = _
    rw [← hend]
    exact apply_reducedWordToRefl q
  have hda := length_rightAdjacentSwap_of_descent g a hu.1
  have hdb := length_rightAdjacentSwap_of_descent g b hv.1
  have hau := ih (g.rightAdjacentSwap a) (by omega) (sortingDistinct_step g a hu.1 hN)
    u (b :: z) hu.2 hlz hsu hls
  have hbv := ih (g.rightAdjacentSwap b) (by omega) (sortingDistinct_step g b hv.1 hN)
    v (a :: z) hv.2 hrz hsv hrs
  have hleft : CommChain ((a :: u).map adjacentLetter) ((a :: b :: z).map adjacentLetter) := by
    simpa only [List.map_cons, List.cons_append, List.nil_append] using
      commChain_prefix [adjacentLetter a] hau
  have hright : CommChain ((b :: v).map adjacentLetter) ((b :: a :: z).map adjacentLetter) := by
    simpa only [List.map_cons, List.cons_append, List.nil_append] using
      commChain_prefix [adjacentLetter b] hbv
  have hmid : WordCommutation ((a :: b :: z).map adjacentLetter)
      ((b :: a :: z).map adjacentLetter) :=
    ⟨[], z.map adjacentLetter, adjacentLetter a, adjacentLetter b, rfl, rfl,
      separatedLetters a b hgap⟩
  exact hleft.trans ((Relation.ReflTransGen.single hmid).trans (commChain_symm hright))

private theorem sorting_commutations (g : FinPermutation n) : AllSortingDistinct g →
    ∀ u v : List (AdjacentPosition n), IsDescendingWord g u → IsDescendingWord g v →
      applyRightAdjacentWord u g = Equiv.refl (Fin n) →
      applyRightAdjacentWord v g = Equiv.refl (Fin n) →
        CommChain (u.map adjacentLetter) (v.map adjacentLetter) := by
  generalize hm : g.length = m
  induction m using Nat.strong_induction_on generalizing g with
  | h m ih =>
    intro hN u v hu hv hsu hsv
    have hind (q : FinPermutation n) (hq : q.length < g.length) :=
      ih q.length (by omega) q rfl
    cases u with
    | nil =>
      change g = Equiv.refl (Fin n) at hsu
      rw [hsu] at hv
      have hvnil := descending_identity_word v hv
      subst v
      exact .refl
    | cons a u =>
      cases v with
      | nil =>
        change g = Equiv.refl (Fin n) at hsv
        rw [hsv] at hu
        have hunil := descending_identity_word (a :: u) hu
        cases hunil
      | cons b v =>
        rcases adjacentPosition_cases a b with heq | hgap | hab | hba
        · subst b
          have hdrop := length_rightAdjacentSwap_of_descent g a hu.1
          have h := hind (g.rightAdjacentSwap a) (by omega)
            (sortingDistinct_step g a hu.1 hN) u v hu.2 hv.2 hsu hsv
          simpa only [List.map_cons, List.cons_append, List.nil_append] using
            commChain_prefix [adjacentLetter a] h
        · exact sorting_comm_of_gap g a b hN hgap u v hu hv hsu hsv hind
        · exact (sortingDistinct_no_braid g a b hN hab hu.1 hv.1).elim
        · exact (sortingDistinct_no_braid g b a hN hba hv.1 hu.1).elim

private theorem sortingDistinct_of_boolean (g : FinPermutation n)
    (hB : IsBoolean (ofFinite n g.symm)) : AllSortingDistinct g := by
  intro word hd hs
  have hp : applyRightAdjacentWord word (Equiv.refl (Fin n)) = g.symm := by
    apply Equiv.ext
    intro k
    apply g.injective
    have hs' := hs
    rw [applyRightAdjacentWord_eq_trans] at hs'
    have he := congrArg (fun q : FinPermutation n => q k) hs'
    change g (applyRightAdjacentWord word (Equiv.refl (Fin n)) k) = k at he
    simpa only [Equiv.apply_symm_apply] using he
  have hl := length_applyRightAdjacentWord_of_isDescending word g hd
  rw [hs, length_refl] at hl
  have hr : IsReducedWord (ofFinite n g.symm) (word.map adjacentLetter) := by
    constructor
    · exact (ofFinite_wordProduct word).symm.trans (congrArg (ofFinite n) hp)
    · calc
        (word.map adjacentLetter).length = word.length := List.length_map _
        _ = g.length := by omega
        _ = Schubert.FinPermutation.length g.symm := (length_symm g).symm
        _ = (ofFinite n g.symm).length := (length_ofFinite n g.symm).symm
  exact hB.reducedWord_nodup hr

/-- Any two reduced expressions of a Boolean permutation are joined by adjacent commutations. -/
theorem IsBoolean.reducedWord_commutations {w : FinitaryPerm ℕ+} (hB : IsBoolean w)
    (u v : List ℕ+) (hu : IsReducedWord w u) (hv : IsReducedWord w v) :
    Relation.ReflTransGen WordCommutation u v := by
  classical
  let s := u.toFinset ∪ v.toFinset
  let n := s.sup PNat.val + 1
  have hUB : ∀ i ∈ u, (i : ℕ) < n := by
    intro i hi
    exact Nat.lt_succ_of_le (Finset.le_sup
      (Finset.mem_union.mpr (Or.inl (List.mem_toFinset.mpr hi)) : i ∈ s))
  have hVB : ∀ i ∈ v, (i : ℕ) < n := by
    intro i hi
    exact Nat.lt_succ_of_le (Finset.le_sup
      (Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr hi)) : i ∈ s))
  obtain ⟨U, hU⟩ := exists_finiteAdjacentWord u hUB
  obtain ⟨V, hV⟩ := exists_finiteAdjacentWord v hVB
  let g := applyRightAdjacentWord U (Equiv.refl (Fin n))
  have hgu : ofFinite n g = w := by rw [ofFinite_wordProduct, hU, hu.1]
  have hgv : applyRightAdjacentWord V (Equiv.refl (Fin n)) = g := by
    apply ofFinite_injective n
    rw [ofFinite_wordProduct, hV, hv.1, hgu]
  have hlen : w.length = g.length := by simpa only [hgu] using length_ofFinite n g
  have hlu : U.length = g.length := by
    calc
      U.length = (U.map adjacentLetter).length := (List.length_map adjacentLetter).symm
      _ = u.length := congrArg List.length hU
      _ = w.length := hu.2
      _ = g.length := hlen
  have hlv : V.length = g.length := by
    calc
      V.length = (V.map adjacentLetter).length := (List.length_map adjacentLetter).symm
      _ = v.length := congrArg List.length hV
      _ = w.length := hv.2
      _ = g.length := hlen
  have hN : AllSortingDistinct g.symm := sortingDistinct_of_boolean g.symm (by
    rw [Equiv.symm_symm, hgu]
    exact hB)
  have hsu : applyRightAdjacentWord U g.symm = Equiv.refl (Fin n) :=
    adjacentWord_sorts_inverse U
  have hsv : applyRightAdjacentWord V g.symm = Equiv.refl (Fin n) := by
    rw [← hgv]
    exact adjacentWord_sorts_inverse V
  have hdu : IsDescendingWord g.symm U := by
    apply isDescendingWord_of_length_eq
    rw [hsu, length_refl, Nat.add_zero, length_symm, hlu]
  have hdv : IsDescendingWord g.symm V := by
    apply isDescendingWord_of_length_eq
    rw [hsv, length_refl, Nat.add_zero, length_symm, hlv]
  have h := sorting_commutations g.symm hN U V hdu hdv hsu hsv
  simpa only [hU, hV] using h

end FinitaryPerm
