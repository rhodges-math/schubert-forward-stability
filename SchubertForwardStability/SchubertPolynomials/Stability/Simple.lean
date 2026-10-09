import SchubertForwardStability.SchubertPolynomials.Basis.Global
import SchubertForwardStability.SchubertPolynomials.Divided.Positive
import SchubertForwardStability.Permutations.Statistics.AdjacentLength

/-! # Initial variable sums and simple Schubert polynomials

## Main definitions

* `initialVariableSum`: the sum of the variables in a finite initial interval.

## Main results

Its adjacent divided differences are boundary indicators. The polynomial of an
adjacent transposition equals the initial variable sum, over every commutative ring.

## Implementation notes

The identification uses homogeneous degree, reduced words and the extraction
duality.
-/

namespace SchubertPolynomial

open FinitaryPerm
open scoped BigOperators Classical

variable {R : Type*} [CommRing R]

/-- Sum of the variables in the first `n` positive positions. -/
noncomputable def initialVariableSum (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial ℕ+ R := ∑ j ∈ positions n, MvPolynomial.X j

/-- The initial variable sum is homogeneous of degree one, including the empty sum. -/
theorem initialVariableSum_isHomogeneous (n : ℕ) :
    (initialVariableSum R n).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  exact MvPolynomial.isHomogeneous_X R j

private theorem dividedDifference_X_indicator (i j : ℕ+) :
    dividedDifference R i (MvPolynomial.X j) =
      (if j = i then 1 else 0) - (if j = i + 1 then 1 else 0) := by
  classical
  have hn : i ≠ i + 1 := by
    intro he
    have hc := congrArg PNat.val he
    change (i : ℕ) = (i : ℕ) + 1 at hc
    omega
  by_cases hj : j = i
  · subst j
    simp only [dividedDifference_X, ite_true, ite_eq_right hn, sub_zero]
  · by_cases hj' : j = i + 1
    · subst j
      simp only [dividedDifference_X_next, ite_eq_right hn.symm, ite_true, zero_sub]
    · simp only [dividedDifference_X_other i j hj hj', ite_eq_right hj,
        ite_eq_right hj', sub_self]

/-- An adjacent operator on an initial sum detects exactly the right boundary. -/
theorem dividedDifference_initialSum (i : ℕ+) (n : ℕ) :
    dividedDifference R i (initialVariableSum R n) = if (i : ℕ) = n then 1 else 0 := by
  classical
  unfold initialVariableSum
  simp only [map_sum, dividedDifference_X_indicator, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', mem_positions]
  change (if (i : ℕ) ≤ n then (1 : MvPolynomial ℕ+ R) else 0) -
    (if (i : ℕ) + 1 ≤ n then 1 else 0) = if (i : ℕ) = n then 1 else 0
  split_ifs <;> simp_all <;> omega

/-- An adjacent transposition's permutation operator is its adjacent divided difference. -/
theorem permutationDivided_simple (i : ℕ+) :
    permutationDividedDifference R (simpleTransposition i) = dividedDifference R i := by
  have hr : IsReducedWord (simpleTransposition i) [i] := by
    simp [IsReducedWord]
  rw [permutationDividedDifference_eq [i] hr, wordDividedDifference_cons,
    wordDividedDifference_nil, LinearMap.comp_id]

private theorem simple_fix_below {i j : ℕ+} (hij : i < j) :
    simpleTransposition j i = i := by
  have hj : j < j + 1 := by change (j : ℕ) < (j : ℕ) + 1; omega
  exact swap_apply_of_ne (ne_of_lt hij) (ne_of_lt (hij.trans hj))

private theorem simple_injective : Function.Injective simpleTransposition := by
  intro i j he
  by_contra hn
  have hv := congrArg (fun w : FinitaryPerm ℕ+ => w (min i j)) he
  rcases lt_or_gt_of_ne hn with hij | hji
  · rw [min_eq_left (le_of_lt hij), simpleTransposition_apply_left,
      simple_fix_below hij] at hv
    have hc := congrArg PNat.val hv
    change (i : ℕ) + 1 = (i : ℕ) at hc
    omega
  · rw [min_eq_right (le_of_lt hji), simple_fix_below hji,
      simpleTransposition_apply_left] at hv
    have hc := congrArg PNat.val hv
    change (j : ℕ) = (j : ℕ) + 1 at hc
    omega

private theorem exists_simple_of_length_one {w : FinitaryPerm ℕ+} (hw : w.length = 1) :
    ∃ i : ℕ+, w = simpleTransposition i := by
  obtain ⟨word, hword⟩ := exists_reducedWordIn w w.isSupported_forwardStability
  have hl : word.length = 1 := hword.1.2.trans hw
  cases word with
  | nil => simp only [List.length_nil] at hl; omega
  | cons i word =>
    have hz : word = [] := List.eq_nil_of_length_eq_zero (by
      simp only [List.length_cons] at hl
      omega)
    subst word
    refine ⟨i, ?_⟩
    simpa only [wordProduct_cons, wordProduct_nil, mul_one] using hword.1.1.symm

/-- Extraction coordinates of an initial variable sum select its boundary transposition. -/
theorem schubertFunctional_initialSum (w : FinitaryPerm ℕ+) (i : ℕ+) :
    schubertFunctional R w (initialVariableSum R (i : ℕ)) =
      if w = simpleTransposition i then 1 else 0 := by
  classical
  by_cases hz : w.length = 0
  · have he : w = 1 := (length_eq_zero_iff w).mp hz
    have hn : (1 : FinitaryPerm ℕ+) ≠ simpleTransposition i := by
      intro hs
      have hl := congrArg FinitaryPerm.length hs
      simp only [length_one, length_simpleTransposition] at hl
      omega
    rw [he, ite_eq_right hn, schubertFunctional_apply, permutationDividedDifference_one,
      LinearMap.id_apply]
    exact (initialVariableSum_isHomogeneous (R := R) (i : ℕ)).coeff_eq_zero (by simp)
  · by_cases ho : w.length = 1
    · obtain ⟨j, he⟩ := exists_simple_of_length_one ho
      rw [he, schubertFunctional_apply, permutationDivided_simple,
        dividedDifference_initialSum]
      by_cases hj : j = i
      · subst j
        simp
      · have hc : (j : ℕ) ≠ (i : ℕ) := fun h => hj (PNat.eq h)
        have hs : simpleTransposition j ≠ simpleTransposition i :=
          fun h => hj (simple_injective h)
        simp only [ite_eq_right hc, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
          ite_eq_right hs]
    · have hl : 1 < w.length := by omega
      have hn : w ≠ simpleTransposition i := by
        intro he
        rw [he, length_simpleTransposition] at ho
        exact ho rfl
      rw [schubertFunctional_apply, permutationDivided_zero_of_degree_lt w
        (initialVariableSum_isHomogeneous (R := R) (i : ℕ)) hl]
      simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, ite_eq_right hn]

/-- A simple Schubert polynomial is the sum of the variables up to its left position. -/
theorem schubert_simpleTransposition (i : ℕ+) :
    schubert R (simpleTransposition i) = ∑ j ∈ positions (i : ℕ), MvPolynomial.X j := by
  apply (schubertBasis R).repr.injective
  apply Finsupp.ext
  intro w
  rw [schubertBasis_repr, schubertBasis_repr, schubertFunctional_schubert]
  exact (schubertFunctional_initialSum (R := R) w i).symm

end SchubertPolynomial
