import SchubertForwardStability.SchubertPolynomials.Coinvariants.ArtinRelations

/-! # Bounded remainders modulo the symmetric ideal

Monic multivariate division by the complete tail relations produces a remainder
whose exponent at finite index i is at most i. The difference from the original
polynomial belongs to the symmetric-generator ideal, over every commutative ring.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

open MvPolynomial
open scoped Classical MonomialOrder

variable {R : Type*} [CommRing R]

private theorem ascending_remainder_nontrivial [Nontrivial R] (n : ℕ)
    (p : MvPolynomial (Fin n) R) :
    ∃ r : MvPolynomial (Fin n) R, p - r ∈ symmetricIdeal R n ∧
      ∀ a ∈ r.support, ∀ i : Fin n, a i ≤ i.val := by
  have hb (i : Fin n) : IsUnit (MonomialOrder.lex.leadingCoeff (triangularRelation R n i)) := by
    rw [(triangularRelation_monic n i).leadingCoeff_eq_one]
    exact isUnit_one
  obtain ⟨g, r, he, _, hr⟩ := MonomialOrder.div hb p
  refine ⟨r, ?_, ?_⟩
  · rw [he, add_sub_cancel_right, Finsupp.linearCombination_apply]
    change (∑ i ∈ g.support, g i * triangularRelation R n i) ∈ symmetricIdeal R n
    exact (symmetricIdeal R n).sum_mem fun i _ =>
      Ideal.mul_mem_left _ _ (triangularRelation_mem n i)
  · intro a ha i
    apply Nat.le_of_lt_succ
    apply Nat.lt_of_not_ge
    intro hle
    apply hr a ha i
    rw [triangularRelation_degree]
    exact Finsupp.single_le_iff.mpr hle

/-- Every finite polynomial has an ascending-exponent remainder modulo the symmetric ideal. -/
theorem exists_ascending_remainder (n : ℕ) (p : MvPolynomial (Fin n) R) :
    ∃ r : MvPolynomial (Fin n) R, p - r ∈ symmetricIdeal R n ∧
      ∀ a ∈ r.support, ∀ i : Fin n, a i ≤ i.val := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · let _ := hs
    refine ⟨0, ?_, by simp⟩
    rw [Subsingleton.elim p 0, sub_self]
    exact (symmetricIdeal R n).zero_mem
  · let _ := hn
    exact ascending_remainder_nontrivial n p

end

end SchubertPolynomial
