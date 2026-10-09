import SchubertForwardStability.SchubertPolynomials.Coinvariants.SignedVariables
import SchubertForwardStability.SchubertPolynomials.Divided.FiniteVariables
import SchubertForwardStability.SchubertPolynomials.Stability.Duality
import SchubertForwardStability.Permutations.Classes.LongestWords

/-! # Signed longest reversal of divided-difference operators

Signed finite-variable reversal embeds as signed longest reversal in positive
variables. It intertwines every bounded adjacent word and supported
permutation operator, and hence transports the extraction functionals.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

open MvPolynomial FinitaryPerm
open scoped Classical

variable {R : Type*} [CommRing R]

/-- Finite signed reversal embeds as positive-indexed signed longest reversal. -/
theorem initialRename_signedRev (n : ℕ) (p : MvPolynomial (Fin n) R) :
    initialRename R n (signedRename R Fin.revPerm p) =
      signedRename R (longestElement n).val (initialRename R n p) := by
  have hindex (i : Fin n) : (positiveIndex n (Fin.revPerm i)).val =
      longestElement n (positiveIndex n i).val := by
    apply PNat.eq
    rw [longestElement_apply_val n _ (positiveIndex n i).property]
    simp only [positiveIndex_val, Fin.revPerm_apply, Fin.val_rev]
    have hi := i.isLt
    omega
  have he : (initialRename R n).comp (signedRename R Fin.revPerm).toAlgHom =
      (signedRename R (longestElement n).val).toAlgHom.comp (initialRename R n) := by
    ext i
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, signedRename_X, map_neg,
      initialRename, rename_X]
    rw [hindex]
  exact AlgHom.congr_fun he p

/-- Signed longest reversal reflects each adjacent divided-difference operator. -/
theorem divided_signed_longest {n : ℕ} {i : ℕ+} (hi : (i : ℕ) < n)
    (p : MvPolynomial ℕ+ R) :
    dividedDifference R (longestElement (n - 1) i)
      (signedRename R (longestElement n).val p) =
        signedRename R (longestElement n).val (dividedDifference R i p) := by
  have h := divided_signedRename (longestElement n).val
    (show i ≠ i + 1 from (show i < i + 1 from Nat.lt_succ_self (i : ℕ)).ne) p
  change variableDividedDifference R (longestElement n (i + 1)) (longestElement n i)
    (signedRename R (longestElement n).val p) = _ at h
  rw [longestElement_next_letter hi, longestElement_left_letter hi] at h
  exact h

/-- Signed longest reversal intertwines every adjacent word in the finite diagram. -/
theorem wordDivided_signed_longest (n : ℕ) (word : List ℕ+)
    (hword : ∀ i ∈ word, (i : ℕ) < n) (p : MvPolynomial ℕ+ R) :
    wordDividedDifference R (word.map (longestElement (n - 1)))
      (signedRename R (longestElement n).val p) =
        signedRename R (longestElement n).val (wordDividedDifference R word p) := by
  induction word generalizing p with
  | nil => rfl
  | cons i word ih =>
    simp only [List.map_cons, wordDividedDifference_cons, LinearMap.comp_apply]
    rw [ih (fun j hj => hword j (List.mem_cons_of_mem i hj))]
    exact divided_signed_longest (hword i List.mem_cons_self) _

/-- Signed longest reversal transports supported permutation divided differences. -/
theorem permutationDivided_signed_longest {n : ℕ} (w : FinitaryPerm ℕ+)
    (hw : IsSupported n w) (p : MvPolynomial ℕ+ R) :
    permutationDividedDifference R (longestElement n * w * longestElement n)
      (signedRename R (longestElement n).val p) =
        signedRename R (longestElement n).val (permutationDividedDifference R w p) := by
  obtain ⟨word, hword⟩ := exists_reducedWordIn w hw
  rw [permutationDividedDifference_eq _ (hword.conjugate_longest hw).1,
    permutationDividedDifference_eq word hword.1]
  exact wordDivided_signed_longest n word hword.2 p

/-- Signed longest reversal transports every supported Schubert extraction functional. -/
theorem schubertFunctional_signed_longest {n : ℕ} (w : FinitaryPerm ℕ+)
    (hw : IsSupported n w) (p : MvPolynomial ℕ+ R) :
    schubertFunctional R (longestElement n * w * longestElement n)
      (signedRename R (longestElement n).val p) = schubertFunctional R w p := by
  rw [schubertFunctional_apply, permutationDivided_signed_longest w hw p,
    schubertFunctional_apply]
  exact constantCoeff_signedRename _ _

end

end SchubertPolynomial
