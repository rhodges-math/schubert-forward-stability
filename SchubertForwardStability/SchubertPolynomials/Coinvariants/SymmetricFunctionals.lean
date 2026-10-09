import SchubertForwardStability.SchubertPolynomials.Coinvariants.SymmetricIdeal
import SchubertForwardStability.SchubertPolynomials.Divided.FiniteVariables
import SchubertForwardStability.SchubertPolynomials.Stability.Duality

/-! # Divided-difference functionals on the symmetric ideal

A symmetric polynomial in the initial finite variable interval factors through
every divided-difference word in that interval. If its constant coefficient is
zero, its multiples have zero supported Schubert coordinates.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

open MvPolynomial FinitaryPerm
open scoped Classical

variable {R : Type*} [CommRing R]

/-- Initial-interval symmetric polynomials have zero divided differences inside the interval. -/
theorem divided_initialRename_symmetric {n : ℕ} {q : MvPolynomial (Fin n) R}
    (hq : q.IsSymmetric) {i : ℕ+} (hi : (i : ℕ) < n) :
    dividedDifference R i (initialRename R n q) = 0 := by
  let a : Fin n := ⟨(i : ℕ) - 1, (Nat.sub_le _ _).trans_lt hi⟩
  let b : Fin n := ⟨i, hi⟩
  let f : Fin n → ℕ+ := fun k => (positiveIndex n k).val
  have hf : Function.Injective f := fun _ _ h =>
    (positiveIndex n).injective (Subtype.ext h)
  have ha : f a = i := PNat.eq (by
    change (i : ℕ) - 1 + 1 = (i : ℕ)
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt i.pos))
  have hb : f b = i + 1 := PNat.eq rfl
  have hab : a ≠ b := by
    intro he
    have hval := congrArg Fin.val he
    have := i.pos
    dsimp only [a, b] at hval
    omega
  have hd : variableDividedDifference R a b q = 0 := by
    apply (variableDividedDifference_eq_zero hab _).mpr
    rw [variableSwap, renameEquiv_apply]
    exact hq _
  change variableDividedDifference R i (i + 1) (rename f q) = 0
  rw [←hb, ←ha, variableDividedDifference_rename f hf hab, hd, map_zero]

/-- A symmetric factor in the initial interval factors through every bounded word operator. -/
theorem wordDivided_initialRename_symmetric {n : ℕ} {q : MvPolynomial (Fin n) R}
    (hq : q.IsSymmetric) (word : List ℕ+) (hword : ∀ i ∈ word, (i : ℕ) < n)
    (p : MvPolynomial ℕ+ R) :
    wordDividedDifference R word (initialRename R n q * p) =
      initialRename R n q * wordDividedDifference R word p := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    have hi := hword i List.mem_cons_self
    have ht : ∀ j ∈ word, (j : ℕ) < n := fun j hj => hword j (List.mem_cons_of_mem _ hj)
    simp only [wordDividedDifference_cons, LinearMap.comp_apply]
    rw [ih ht, dividedDifference_mul, divided_initialRename_symmetric hq hi, zero_mul,
      zero_add]
    have hs : variableSwap R i (i + 1) (initialRename R n q) = initialRename R n q :=
      (variableDividedDifference_eq_zero (by
        exact (show i < i + 1 from Nat.lt_succ_self (i : ℕ)).ne) _).mp
        (divided_initialRename_symmetric hq hi)
    rw [hs]

/-- Supported permutation operators factor through symmetric initial-interval factors. -/
theorem permutationDivided_symmetric {n : ℕ} {q : MvPolynomial (Fin n) R}
    (hq : q.IsSymmetric) (w : FinitaryPerm ℕ+) (hw : IsSupported n w)
    (p : MvPolynomial ℕ+ R) :
    permutationDividedDifference R w (initialRename R n q * p) =
      initialRename R n q * permutationDividedDifference R w p := by
  obtain ⟨word, hword, hbound⟩ := exists_reducedWordIn w hw
  rw [permutationDividedDifference_eq word hword]
  exact wordDivided_initialRename_symmetric hq word hbound p

/-- A zero-constant symmetric factor annihilates all supported extraction functionals. -/
theorem schubertFunctional_symmetric_mul {n : ℕ} {q : MvPolynomial (Fin n) R}
    (hq : q.IsSymmetric) (hc : constantCoeff q = 0) (w : FinitaryPerm ℕ+)
    (hw : IsSupported n w) (p : MvPolynomial ℕ+ R) :
    schubertFunctional R w (initialRename R n q * p) = 0 := by
  rw [schubertFunctional_apply, permutationDivided_symmetric hq w hw p]
  change constantCoeff (initialRename R n q * permutationDividedDifference R w p) = 0
  rw [map_mul, constantCoeff_rename, hc, zero_mul]

/-- Every polynomial in the symmetric-generator ideal has zero supported Schubert coordinates. -/
theorem schubertFunctional_symmetricIdeal {n : ℕ} {q : MvPolynomial (Fin n) R}
    (hq : q ∈ symmetricIdeal R n) (w : FinitaryPerm ℕ+) (hw : IsSupported n w) :
    schubertFunctional R w (initialRename R n q) = 0 := by
  have hmul : ∀ a : MvPolynomial (Fin n) R,
      schubertFunctional R w (initialRename R n (q * a)) = 0 := by
    induction hq using Submodule.span_induction with
    | mem p hp =>
      intro a
      rw [map_mul]
      exact schubertFunctional_symmetric_mul hp.1 hp.2 w hw _
    | zero => intro a; simp
    | add p q _ _ hp hq =>
      intro a
      rw [add_mul, map_add, map_add, hp a, hq a, add_zero]
    | smul r p _ hp =>
      intro a
      change schubertFunctional R w (initialRename R n ((r * p) * a)) = 0
      rw [mul_assoc, mul_left_comm r p a]
      exact hp (r * a)
  simpa only [mul_one] using hmul 1

end

end SchubertPolynomial
