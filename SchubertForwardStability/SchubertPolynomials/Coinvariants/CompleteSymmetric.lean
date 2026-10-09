import SchubertForwardStability.SchubertPolynomials.Coinvariants.SymmetricIdeal
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Complete symmetric sums and deletion of a variable

Complete homogeneous symmetric polynomials are sums over multisets of fixed size.
Separating the multisets containing a distinguished variable gives the variable
deletion recurrence used in the triangular coinvariant relations.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

open MvPolynomial
open scoped Classical

variable {σ τ R S : Type*} [DecidableEq σ] [DecidableEq τ] [Fintype σ] [Fintype τ]
  [CommSemiring R] [CommSemiring S]

/-- Evaluate the degree-k complete symmetric sum at a finite variable family. -/
def completeSymmetricValue (f : σ → S) (k : ℕ) : S :=
  ∑ s : Sym σ k, (s.1.map f).prod

/-- The degree-zero complete symmetric sum is one. -/
@[simp] theorem completeSymmetricValue_zero_degree (f : σ → S) :
    completeSymmetricValue f 0 = 1 := by
  simp [completeSymmetricValue, Sym.eq_nil_of_card_zero]

/-- A positive-degree complete symmetric sum on an empty family is zero. -/
theorem completeSymmetricValue_empty [IsEmpty σ] (f : σ → S) {k : ℕ} (hk : 0 < k) :
    completeSymmetricValue f k = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp [completeSymmetricValue]

/-- The complete symmetric polynomial evaluated at a family is its multiset sum. -/
theorem aeval_hsymm [Algebra R S] (f : σ → S) (k : ℕ) :
    aeval f (hsymm σ R k) = completeSymmetricValue f k := by
  simp only [hsymm, map_sum, ←Multiset.prod_hom', aeval_X, completeSymmetricValue]

/-- Complete symmetric sums are unchanged by a reindexing equivalence. -/
theorem completeSymmetricValue_equiv (e : σ ≃ τ) (f : τ → S) (k : ℕ) :
    completeSymmetricValue (fun i => f (e i)) k = completeSymmetricValue f k := by
  unfold completeSymmetricValue
  apply Fintype.sum_equiv (Sym.equivCongr e)
  intro s
  simp [Sym.equivCongr, Sym.map, Multiset.map_map]

/-- Separating multisets containing the distinguished variable gives the deletion recurrence. -/
theorem completeSymmetricValue_option (f : Option σ → S) (k : ℕ) :
    completeSymmetricValue f (k + 1) =
      f none * completeSymmetricValue f k +
        completeSymmetricValue (fun i => f (some i)) (k + 1) := by
  calc
    completeSymmetricValue f (k + 1) =
        ∑ s : Sym (Option σ) k ⊕ Sym σ (k + 1),
          ((SymOptionSuccEquiv.decode s).1.map f).prod := by
      exact Fintype.sum_equiv (symOptionSuccEquiv (α := σ) (n := k))
        (fun s : Sym (Option σ) (k + 1) => (s.1.map f).prod)
        (fun s : Sym (Option σ) k ⊕ Sym σ (k + 1) =>
          ((SymOptionSuccEquiv.decode s).1.map f).prod)
        (fun s => congrArg (fun t : Sym (Option σ) (k + 1) => (t.1.map f).prod)
          (SymOptionSuccEquiv.decode_encode s).symm)
    _ = _ := by
      simp only [Fintype.sum_sum_type, SymOptionSuccEquiv.decode_inl,
        SymOptionSuccEquiv.decode_inr, Sym.cons, Multiset.map_cons, Multiset.prod_cons,
        Sym.map, Multiset.map_map, Function.comp_apply, Function.Embedding.some_apply,
        ←Finset.mul_sum,
        completeSymmetricValue]

/-- A positive-degree complete symmetric sum evaluated at zeros is zero. -/
theorem completeSymmetricValue_zero {k : ℕ} (hk : 0 < k) :
    completeSymmetricValue (fun _ : σ => (0 : S)) k = 0 := by
  unfold completeSymmetricValue
  apply Finset.sum_eq_zero
  intro s _
  simp only [Multiset.map_const', s.2, Multiset.prod_replicate, zero_pow hk.ne']

/-- Deleting the first member of a finite family gives the complete-symmetric recurrence. -/
theorem completeSymmetricValue_fin {n : ℕ} (f : Fin (n + 1) → S) (k : ℕ) :
    completeSymmetricValue f (k + 1) = f 0 * completeSymmetricValue f k +
      completeSymmetricValue (fun i : Fin n => f i.succ) (k + 1) := by
  let g : Option (Fin n) → S := fun i => f ((finSuccEquiv n).symm i)
  have he (j : ℕ) : completeSymmetricValue g j = completeSymmetricValue f j :=
    completeSymmetricValue_equiv (finSuccEquiv n).symm f j
  have hr := completeSymmetricValue_option g k
  simp only [he] at hr
  simpa only [g, finSuccEquiv_symm_none, finSuccEquiv_symm_some] using hr

/-- Every positive-degree complete symmetric polynomial has zero constant coefficient. -/
theorem constantCoeff_hsymm_pos {n k : ℕ} (hk : 0 < k) :
    constantCoeff (hsymm (Fin n) R k) = 0 := by
  simp only [hsymm, map_sum, ←Multiset.prod_hom', constantCoeff_X]
  exact completeSymmetricValue_zero hk

/-- Positive-degree complete symmetric polynomials belong to the symmetric-generator ideal. -/
theorem hsymm_mem_symmetricIdeal {R : Type*} [CommRing R] {n k : ℕ} (hk : 0 < k) :
    hsymm (Fin n) R k ∈ symmetricIdeal R n :=
  Ideal.subset_span ⟨hsymm_isSymmetric (Fin n) R k, constantCoeff_hsymm_pos hk⟩

end

end SchubertPolynomial
