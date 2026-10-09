import SchubertForwardStability.SchubertPolynomials.Coinvariants.CompleteSymmetric
import Lean.Elab.Tactic.Omega

/-! # Triangular relations in the symmetric ideal

After deleting r variables, every complete symmetric polynomial of degree
greater than r belongs to the full symmetric-generator ideal. In particular,
the degree-(r+1) polynomial in the remaining variables is a triangular relation.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

open MvPolynomial
open scoped Classical

variable {R : Type*} [CommRing R]

/-- Embed a finite interval after an offset into an ambient finite variable interval. -/
def offsetVariable {n r m : ℕ} (h : r + m ≤ n) (i : Fin m) : Fin n :=
  ⟨r + i.val, by omega⟩

/-- Removing one variable raises the threshold for complete-symmetric ideal membership by one. -/
theorem completeSymmetricValue_tail_mem {A : Type*} [CommRing A] (I : Ideal A)
    {m r k : ℕ} (f : Fin (m + 1) → A)
    (hf : ∀ j : ℕ, r < j → completeSymmetricValue f j ∈ I) (hk : r + 1 < k) :
    completeSymmetricValue (fun i : Fin m => f i.succ) k ∈ I := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hr := completeSymmetricValue_fin f j
  have he : completeSymmetricValue (fun i : Fin m => f i.succ) (j + 1) =
      completeSymmetricValue f (j + 1) - f 0 * completeSymmetricValue f j := by
    rw [hr, add_sub_cancel_left]
  rw [he]
  exact I.sub_mem (hf _ (by omega)) (I.mul_mem_left _ (hf _ (by omega)))

/-- Complete symmetric sums in a tail interval of degree above its offset lie in the ideal. -/
theorem completeSymmetricValue_offset_mem {n r m k : ℕ} (hn : r + m = n) (hk : r < k) :
    completeSymmetricValue (fun i : Fin m => (X (offsetVariable hn.le i) :
      MvPolynomial (Fin n) R)) k ∈ symmetricIdeal R n := by
  induction r generalizing m k with
  | zero =>
    have hm : m = n := by omega
    subst m
    have he : (fun i : Fin n => (X (offsetVariable hn.le i) : MvPolynomial (Fin n) R)) =
        fun i => X i := by
      funext i
      congr 1
      exact Fin.ext (by simp [offsetVariable])
    rw [he]
    exact hsymm_mem_symmetricIdeal hk
  | succ r ih =>
    have hb : r + (m + 1) = n := by omega
    let f (i : Fin (m + 1)) := (X (offsetVariable hb.le i) : MvPolynomial (Fin n) R)
    have hf (j : ℕ) (hj : r < j) : completeSymmetricValue f j ∈ symmetricIdeal R n :=
      ih hb hj
    have he : (fun i : Fin m => f i.succ) =
        fun i => (X (offsetVariable hn.le i) : MvPolynomial (Fin n) R) := by
      funext i
      dsimp only [f]
      apply congrArg (fun j : Fin n => (X j : MvPolynomial (Fin n) R))
      exact Fin.ext (by dsimp [offsetVariable]; omega)
    have ht : completeSymmetricValue (fun i : Fin m => f i.succ) k ∈ symmetricIdeal R n :=
      completeSymmetricValue_tail_mem (symmetricIdeal R n) f hf (by omega)
    rw [he] at ht
    exact ht

/-- Complete homogeneous tail polynomials above the offset belong to the symmetric ideal. -/
theorem rename_hsymm_offset_mem {n r m k : ℕ} (hn : r + m = n) (hk : r < k) :
    rename (offsetVariable hn.le) (hsymm (Fin m) R k) ∈ symmetricIdeal R n := by
  rw [rename_eq_aeval, aeval_hsymm]
  exact completeSymmetricValue_offset_mem hn hk

/-- The degree-(r+1) complete tail relation belongs to the symmetric ideal. -/
theorem triangular_hsymm_mem {n r m : ℕ} (hn : r + m = n) :
    rename (offsetVariable hn.le) (hsymm (Fin m) R (r + 1)) ∈ symmetricIdeal R n :=
  rename_hsymm_offset_mem hn (Nat.lt_succ_self r)

end

end SchubertPolynomial
