import SchubertForwardStability.SchubertPolynomials.Divided.Independence

/-! # Vanishing of unreduced divided-difference words

## Main results

Every word longer than the inversion length of its permutation product has zero
divided-difference operator, both for finite and positive-indexed variables.

## Implementation notes

Induction removes the last letter. At the first length drop, reduced-word independence
replaces the preceding expression by one ending in that letter, and square zero applies.

## References

L. Manivel, *Symmetric functions, Schubert polynomials and degeneracy loci*, Sections 2.3--2.5.
-/

namespace SchubertPolynomial

open Schubert.FinPermutation

variable {n : ℕ} {R : Type*} [CommRing R]

/-- A finite adjacent word which is not length-minimal has zero divided-difference operator. -/
theorem finiteWordDividedDifference_zero (word : List (AdjacentPosition n)) :
    (applyRightAdjacentWord word (Equiv.refl (Fin n))).length ≠ word.length →
      finiteWordDividedDifference R word = 0 := by
  induction word using List.reverseRecOn with
  | nil =>
    intro hne
    exact False.elim (hne (length_refl n))
  | append_singleton word a ih =>
    intro hne
    let g := applyRightAdjacentWord word (Equiv.refl (Fin n))
    have hfull : applyRightAdjacentWord (word ++ [a]) (Equiv.refl (Fin n)) =
        g.rightAdjacentSwap a := by
      rw [applyRightAdjacentWord_append]
      rfl
    by_cases hshort : g.length ≠ word.length
    · rw [finiteWordDividedDifference_append, ih hshort]
      exact LinearMap.zero_comp _
    · have hlen : g.length = word.length := not_not.mp hshort
      have hdesc : g.HasDescent a.left := by
        rcases descent_or_ascent g a with hdesc | hascent
        · exact hdesc
        · have hrise := length_rightAdjacentSwap_of_ascent g a hascent
          exfalso
          apply hne
          calc (applyRightAdjacentWord (word ++ [a]) (Equiv.refl (Fin n))).length =
              (g.rightAdjacentSwap a).length := congrArg length hfull
            _ = g.length + 1 := hrise.symm
            _ = (word ++ [a]).length := by rw [hlen, List.length_append]; rfl
      let z := reducedWordToRefl (g.rightAdjacentSwap a).symm
      have hz : applyRightAdjacentWord z (Equiv.refl (Fin n)) = g.rightAdjacentSwap a :=
        applyRightAdjacentWord_refl_eq_symm_of_eq_refl
          (apply_reducedWordToRefl (g.rightAdjacentSwap a).symm)
      have hza : applyRightAdjacentWord (z ++ [a]) (Equiv.refl (Fin n)) = g := by
        rw [applyRightAdjacentWord_append, hz, applyRightAdjacentWord_cons,
          applyRightAdjacentWord_nil, rightAdjacentSwap_involutive]
      have hzlen : z.length = (g.rightAdjacentSwap a).length := by
        rw [length_reducedWordToRefl, length_symm]
      have hzalen : (z ++ [a]).length = g.length := by
        rw [List.length_append, List.length_singleton, hzlen]
        exact length_rightAdjacentSwap_of_descent g a hdesc
      have heq := finiteWordDividedDifference_eq (R := R) g word (z ++ [a]) rfl hza
        hlen.symm hzalen
      rw [finiteWordDividedDifference_append, heq, finiteWordDividedDifference_append]
      apply LinearMap.ext
      intro p
      change finiteWordDividedDifference R z
        (finiteDividedDifference R a (finiteDividedDifference R a p)) = 0
      rw [variableDividedDifference_sq a.left_ne_right, map_zero]

/-- Unreduced positive words give zero operators, as in Manivel, Sections 2.3--2.5. -/
theorem wordDividedDifference_zero (word : List ℕ+)
    (hword : ¬ FinitaryPerm.IsReducedWord (FinitaryPerm.wordProduct word) word) :
    wordDividedDifference R word = 0 := by
  classical
  apply LinearMap.ext
  intro p
  change wordDividedDifference R word p = 0
  let bound := (word.toFinset.sup fun i => (i : ℕ)) + 1
  obtain ⟨n, hn, q, hq⟩ := exists_initialRename p bound
  have hbound : ∀ i ∈ word, (i : ℕ) < n := by
    intro i hi
    have hib := Finset.le_sup (f := fun i : ℕ+ => (i : ℕ)) (List.mem_toFinset.mpr hi)
    dsimp [bound] at hn
    omega
  obtain ⟨wf, hwf⟩ := FinitaryPerm.exists_finiteAdjacentWord word hbound
  let g := applyRightAdjacentWord wf (Equiv.refl (Fin n))
  have hgu : FinitaryPerm.ofFinite n g = FinitaryPerm.wordProduct word := by
    rw [FinitaryPerm.ofFinite_wordProduct, hwf]
  have hne : g.length ≠ wf.length := by
    intro heq
    apply hword
    refine ⟨rfl, ?_⟩
    calc word.length = wf.length := by rw [← hwf, List.length_map]
      _ = g.length := heq.symm
      _ = (FinitaryPerm.ofFinite n g).length := (FinitaryPerm.length_ofFinite n g).symm
      _ = (FinitaryPerm.wordProduct word).length := congrArg FinitaryPerm.length hgu
  have hz := finiteWordDividedDifference_zero (R := R) wf hne
  have h := congrArg (fun op : Module.End R (MvPolynomial (Fin n) R) =>
    initialRename R n (op q)) hz
  simp only [← initialRename_wordDividedDifference, LinearMap.zero_apply, map_zero] at h
  change wordDividedDifference R (wf.map FinitaryPerm.adjacentLetter) (initialRename R n q) =
    0 at h
  simpa only [hwf, hq] using h

end SchubertPolynomial
