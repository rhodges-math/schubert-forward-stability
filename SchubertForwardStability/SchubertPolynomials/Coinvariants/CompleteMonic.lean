import SchubertForwardStability.SchubertPolynomials.Coinvariants.TriangularRelations
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Order.Fin.Basic

/-! # Monic leading terms of complete tail relations

For an increasing nonempty family of variable indices, the complete homogeneous
polynomial of degree k is lexicographically monic with leading monomial the kth
power of the first variable. This identifies the pure powers excluded from the
remainders of monic multivariate division by the triangular relations.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

open MvPolynomial
open scoped Classical MonomialOrder

variable {R : Type*} [CommRing R]

private theorem lex_single_lt {n : ℕ} {i j : Fin n} (hij : i < j) {k : ℕ} (hk : 0 < k) :
    Finsupp.single j k ≺[MonomialOrder.lex] Finsupp.single i k := by
  rw [MonomialOrder.lex_lt_iff]
  refine ⟨i, ?_, ?_⟩
  · intro a ha
    simp only [ofLex_toLex, Finsupp.single_eq_of_ne ha.ne,
      Finsupp.single_eq_of_ne (ha.trans hij).ne]
  · simp only [ofLex_toLex, Finsupp.single_eq_of_ne hij.ne, Finsupp.single_eq_same]
    exact hk

private theorem lex_X_mul_pair [Nontrivial R] {n k : ℕ} (i : Fin n)
    {p : MvPolynomial (Fin n) R} (hp : MonomialOrder.lex.Monic p)
    (hd : MonomialOrder.lex.degree p = Finsupp.single i k) :
    MonomialOrder.lex.Monic (X i * p) ∧
      MonomialOrder.lex.degree (X i * p) = Finsupp.single i (k + 1) := by
  refine ⟨MonomialOrder.Monic.mul MonomialOrder.monic_X hp, ?_⟩
  rw [MonomialOrder.degree_mul_of_mul_leadingCoeff_ne_zero, MonomialOrder.degree_X, hd]
  · rw [←Finsupp.single_add, add_comm 1 k]
  · simp only [MonomialOrder.leadingCoeff_X, hp.leadingCoeff_eq_one, mul_one, ne_eq,
      one_ne_zero, not_false_eq_true]

private theorem complete_lex_pair [Nontrivial R] {n m : ℕ} (f : Fin (m + 1) → Fin n)
    (hf : StrictMono f) (k : ℕ) :
    MonomialOrder.lex.Monic (completeSymmetricValue (fun i => (X (f i) :
      MvPolynomial (Fin n) R)) k) ∧
      MonomialOrder.lex.degree (completeSymmetricValue (fun i =>
        (X (f i) : MvPolynomial (Fin n) R)) k) = Finsupp.single (f 0) k := by
  induction m generalizing k with
  | zero =>
    induction k with
    | zero => simp only [completeSymmetricValue_zero_degree, MonomialOrder.monic_one,
        MonomialOrder.degree_one, Finsupp.single_zero, and_self]
    | succ k ih =>
      rw [completeSymmetricValue_fin, completeSymmetricValue_empty _ (Nat.succ_pos _),
        add_zero]
      exact lex_X_mul_pair _ ih.1 ih.2
  | succ m ih =>
    have ht : StrictMono (fun i : Fin (m + 1) => f i.succ) := hf.comp Fin.strictMono_succ
    induction k with
    | zero => simp only [completeSymmetricValue_zero_degree, MonomialOrder.monic_one,
        MonomialOrder.degree_one, Finsupp.single_zero, and_self]
    | succ k hk =>
      have hfirst := lex_X_mul_pair (f 0) hk.1 hk.2
      have htail := ih (fun i : Fin (m + 1) => f i.succ) ht (k + 1)
      have hlt : MonomialOrder.lex.degree (completeSymmetricValue
          (fun i : Fin (m + 1) => (X (f i.succ) : MvPolynomial (Fin n) R)) (k + 1))
          ≺[MonomialOrder.lex] MonomialOrder.lex.degree (X (f 0) *
            completeSymmetricValue (fun i => (X (f i) : MvPolynomial (Fin n) R)) k) := by
        rw [htail.2, hfirst.2]
        exact lex_single_lt (hf (show (0 : Fin (m + 2)) < (0 : Fin (m + 1)).succ from
          by change (0 : ℕ) < 1; decide)) (Nat.succ_pos k)
      rw [completeSymmetricValue_fin]
      exact ⟨hfirst.1.add_of_lt hlt, (MonomialOrder.degree_add_of_lt hlt).trans hfirst.2⟩

/-- A complete homogeneous polynomial on increasing variables has its first pure power as degree. -/
theorem complete_lex_degree [Nontrivial R] {n m : ℕ} (f : Fin (m + 1) → Fin n)
    (hf : StrictMono f) (k : ℕ) :
    MonomialOrder.lex.degree (completeSymmetricValue (fun i => (X (f i) :
      MvPolynomial (Fin n) R)) k) = Finsupp.single (f 0) k :=
  (complete_lex_pair f hf k).2

/-- Complete homogeneous polynomials on increasing variables are lexicographically monic. -/
theorem complete_lex_monic {n m : ℕ} (f : Fin (m + 1) → Fin n) (hf : StrictMono f) (k : ℕ) :
    MonomialOrder.lex.Monic (completeSymmetricValue (fun i =>
      (X (f i) : MvPolynomial (Fin n) R)) k) := by
  nontriviality R
  exact (complete_lex_pair f hf k).1

end

end SchubertPolynomial
