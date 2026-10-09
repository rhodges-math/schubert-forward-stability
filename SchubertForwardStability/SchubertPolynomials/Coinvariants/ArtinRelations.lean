import SchubertForwardStability.SchubertPolynomials.Coinvariants.CompleteMonic

/-! # Monic triangular generators in finite variables

The complete homogeneous tail polynomial indexed by i has degree i+1,
belongs to the symmetric-generator ideal, and has pure leading monomial
X_i^(i+1) for lexicographic order. Monicity holds over every coefficient ring;
the displayed leading exponent requires a nontrivial coefficient ring.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

open MvPolynomial
open scoped Classical MonomialOrder

variable {R : Type*} [CommRing R]

/-- The natural offset embedding is strictly increasing on finite indices. -/
theorem offsetVariable_strictMono {n r m : ℕ} (h : r + m ≤ n) :
    StrictMono (offsetVariable h) := by
  intro i j hij
  change r + i.val < r + j.val
  exact Nat.add_lt_add_left hij r

/-- The degree-(i+1) complete polynomial in variables i through n-1. -/
def triangularRelation (R : Type*) [CommRing R] (n : ℕ) (i : Fin n) : MvPolynomial (Fin n) R :=
  rename (offsetVariable (n := n) (r := i.val) (m := n - (i.val + 1) + 1)
    (by have hi := i.isLt; omega))
    (hsymm (Fin (n - (i.val + 1) + 1)) R (i.val + 1))

/-- Every triangular complete tail polynomial belongs to the original symmetric ideal. -/
theorem triangularRelation_mem (n : ℕ) (i : Fin n) :
    triangularRelation R n i ∈ symmetricIdeal R n := by
  apply triangular_hsymm_mem
  have hi := i.isLt
  omega

/-- The triangular complete tail polynomials are lexicographically monic over every ring. -/
theorem triangularRelation_monic (n : ℕ) (i : Fin n) :
    MonomialOrder.lex.Monic (triangularRelation R n i) := by
  unfold triangularRelation
  rw [rename_eq_aeval, aeval_hsymm]
  exact complete_lex_monic _ (offsetVariable_strictMono _) _

/-- In a nontrivial ring, the leading exponent of the ith relation is the pure (i+1) power. -/
theorem triangularRelation_degree [Nontrivial R] (n : ℕ) (i : Fin n) :
    MonomialOrder.lex.degree (triangularRelation R n i) = Finsupp.single i (i.val + 1) := by
  unfold triangularRelation
  rw [rename_eq_aeval, aeval_hsymm]
  simp only [Function.comp_def]
  rw [complete_lex_degree _ (offsetVariable_strictMono _)]
  congr 1

end

end SchubertPolynomial
