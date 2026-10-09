import SchubertForwardStability.SchubertPolynomials.Divided.FiniteWords
import SchubertForwardStability.Permutations.Classes.FiniteWords
import SchubertForwardStability.Permutations.Classes.LexWord

/-! # Reduced-word independence for finitary divided differences

## Main definitions

* `permutationDividedDifference`: the word-independent operator of a finitary permutation.

## Main results

All reduced positive words for the same permutation give the same operator.
The permutation operator agrees with every reduced expression, over any commutative ring.

## Implementation notes

A common finite interval contains the polynomial variables and both word alphabets.
Finite reduced-word independence passes through the injective variable embedding.
The definition uses the lexicographic selector, but its value is independent of that choice.

## References

L. Manivel, *Symmetric functions, Schubert polynomials and degeneracy loci*, Sections 2.3--2.5.
-/

namespace SchubertPolynomial

open Schubert.FinPermutation

variable {R : Type*} [CommRing R]

/-- All reduced positive-index words give equal operators, as in Manivel, Sections 2.3--2.5. -/
theorem wordDividedDifference_eq {w : FinitaryPerm ℕ+} (u v : List ℕ+)
    (hu : FinitaryPerm.IsReducedWord w u) (hv : FinitaryPerm.IsReducedWord w v) :
    wordDividedDifference R u = wordDividedDifference R v := by
  classical
  apply LinearMap.ext
  intro p
  let bound := max (u.toFinset.sup fun i => (i : ℕ)) (v.toFinset.sup fun i => (i : ℕ)) + 1
  obtain ⟨n, hn, q, hq⟩ := exists_initialRename p bound
  have hub : ∀ i ∈ u, (i : ℕ) < n := by
    intro i hi
    have hiu := Finset.le_sup (f := fun i : ℕ+ => (i : ℕ)) (List.mem_toFinset.mpr hi)
    dsimp [bound] at hn
    omega
  have hvb : ∀ i ∈ v, (i : ℕ) < n := by
    intro i hi
    have hiv := Finset.le_sup (f := fun i : ℕ+ => (i : ℕ)) (List.mem_toFinset.mpr hi)
    dsimp [bound] at hn
    omega
  obtain ⟨uf, huf⟩ := FinitaryPerm.exists_finiteAdjacentWord u hub
  obtain ⟨vf, hvf⟩ := FinitaryPerm.exists_finiteAdjacentWord v hvb
  let g := applyRightAdjacentWord uf (Equiv.refl (Fin n))
  have hgu : FinitaryPerm.ofFinite n g = w := by
    rw [FinitaryPerm.ofFinite_wordProduct, huf, hu.1]
  have hgv : applyRightAdjacentWord vf (Equiv.refl (Fin n)) = g := by
    apply FinitaryPerm.ofFinite_injective n
    rw [FinitaryPerm.ofFinite_wordProduct, hvf, hv.1]
    exact hgu.symm
  have hulu : uf.length = g.length := by
    calc uf.length = u.length := by rw [← huf, List.length_map]
      _ = w.length := hu.2
      _ = g.length := by rw [← hgu, FinitaryPerm.length_ofFinite]
  have hvlu : vf.length = g.length := by
    calc vf.length = v.length := by rw [← hvf, List.length_map]
      _ = w.length := hv.2
      _ = g.length := by rw [← hgu, FinitaryPerm.length_ofFinite]
  have hfinite := finiteWordDividedDifference_eq (R := R) g uf vf rfl hgv hulu hvlu
  have h := congrArg (fun op : Module.End R (MvPolynomial (Fin n) R) =>
    initialRename R n (op q)) hfinite
  simp only [← initialRename_wordDividedDifference] at h
  change wordDividedDifference R (uf.map FinitaryPerm.adjacentLetter) (initialRename R n q) =
    wordDividedDifference R (vf.map FinitaryPerm.adjacentLetter) (initialRename R n q) at h
  simpa only [huf, hvf, hq] using h

/-- The divided-difference operator associated with a finitary permutation. -/
noncomputable def permutationDividedDifference (R : Type*) [CommRing R]
    (w : FinitaryPerm ℕ+) : Module.End R (MvPolynomial ℕ+ R) :=
  wordDividedDifference R w.lexFirstReducedWord

/-- The permutation operator can be evaluated along any reduced expression. -/
theorem permutationDividedDifference_eq {w : FinitaryPerm ℕ+} (word : List ℕ+)
    (hword : FinitaryPerm.IsReducedWord w word) :
    permutationDividedDifference R w = wordDividedDifference R word :=
  wordDividedDifference_eq _ _ (FinitaryPerm.isReducedWordIn_lexFirst w).1 hword

/-- The identity permutation's divided-difference operator is identity. -/
theorem permutationDividedDifference_one :
    permutationDividedDifference R (1 : FinitaryPerm ℕ+) = LinearMap.id := by
  rw [permutationDividedDifference, FinitaryPerm.lexFirstReducedWord_one,
    wordDividedDifference_nil]

end SchubertPolynomial
