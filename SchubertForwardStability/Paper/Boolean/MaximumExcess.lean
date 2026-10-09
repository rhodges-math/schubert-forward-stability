import SchubertForwardStability.Paper.Boolean.Means
import SchubertForwardStability.Paper.Uniform.MaximumGap

/-! # Finite maximum excess above a terminal record walk

The terminal increment contributes at most one. Each earlier position contributes
its positive excess, and finite uniform integration preserves the resulting bound.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

/-- The ambient maximum is bounded by the last supported value and earlier positive excesses. -/
theorem recordWalkMaxAt_le_positive_excess (r : ℕ+) (u v : FinitaryPerm ℕ+) :
    (recordWalkMaxAt (r : ℕ) u v : ℝ) ≤ (recordWalk u v r : ℝ) + 1 +
      ∑ i ∈ positions ((r : ℕ) - 1), max ((recordWalk u v i : ℝ) - recordWalk u v r) 0 := by
  obtain ⟨i, hi, he⟩ := exists_recordWalk_eq_maxAt (r : ℕ) u v
  rw [← he]
  have hSum : (0 : ℝ) ≤
      ∑ j ∈ positions ((r : ℕ) - 1), max ((recordWalk u v j : ℝ) - recordWalk u v r) 0 :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  by_cases hBefore : (i : ℕ) < (r : ℕ)
  · have hMem : i ∈ positions ((r : ℕ) - 1) :=
      (mem_positions _ _).mpr (by omega)
    have hOne := Finset.single_le_sum
      (f := fun j : ℕ+ => max ((recordWalk u v j : ℝ) - recordWalk u v r) 0)
      (fun j _ => le_max_right _ _) hMem
    have hPart := le_max_left ((recordWalk u v i : ℝ) - recordWalk u v r) 0
    linarith
  · by_cases hEq : i = r
    · rw [hEq]
      linarith
    · have hNext : i = r + 1 := by
        apply PNat.eq
        change (i : ℕ) = (r : ℕ) + 1
        have hNe : (i : ℕ) ≠ (r : ℕ) := fun h => hEq (PNat.eq h)
        omega
      rw [hNext]
      have hStep : (recordWalk u v (r + 1) : ℝ) - recordWalk u v r ≤ 1 := by
        exact_mod_cast (recordWalkStep_bounds u v r).2
      linarith

/-- The expected Boolean ambient maximum is controlled by the sum of expected positive excesses. -/
theorem integral_boolean_maxAt_le_excess (r : ℕ+) :
    (∫ p, (recordWalkMaxAt (r : ℕ) p.1 p.2 : ℝ) ∂pairLaw (boolean (r : ℕ))) ≤
      booleanMeanWalk (r : ℕ) r + 1 + ∑ i ∈ positions ((r : ℕ) - 1),
        ∫ p, max ((recordWalk p.1 p.2 i : ℝ) - recordWalk p.1 p.2 r) 0
          ∂pairLaw (boolean (r : ℕ)) := by
  calc
    _ ≤ ∫ p, (recordWalk p.1 p.2 r : ℝ) + 1 +
        ∑ i ∈ positions ((r : ℕ) - 1),
          max ((recordWalk p.1 p.2 i : ℝ) - recordWalk p.1 p.2 r) 0
          ∂pairLaw (boolean (r : ℕ)) := by
      apply integral_uniform_finset_mono
      intro p _
      exact recordWalkMaxAt_le_positive_excess r p.1 p.2
    _ = _ := by
      have hMass : (uniformOn (((boolean (r : ℕ)).product (boolean (r : ℕ))) :
          Set (FinitaryPerm ℕ+ × FinitaryPerm ℕ+))).real Set.univ = 1 := by
        change (pairLaw (boolean (r : ℕ))).real Set.univ = 1
        exact probReal_univ
      simp only [booleanMeanWalk, pairLaw]
      rw [integral_uniform_finset_add, integral_uniform_finset_add,
        integral_uniform_finsetSum]
      simp only [integral_const, smul_eq_mul, hMass, one_mul]

/-- Boolean product forward stability itself has the same positive-excess upper bound. -/
theorem integral_boolean_product_le_excess (r : ℕ+) :
    (∫ p, (SchubertPolynomial.productForwardStability p.1 p.2 : ℝ)
      ∂pairLaw (boolean (r : ℕ))) ≤ booleanMeanWalk (r : ℕ) r + 1 +
      ∑ i ∈ positions ((r : ℕ) - 1),
        ∫ p, max ((recordWalk p.1 p.2 i : ℝ) - recordWalk p.1 p.2 r) 0
          ∂pairLaw (boolean (r : ℕ)) := by
  apply le_trans _ (integral_boolean_maxAt_le_excess r)
  apply integral_uniform_finset_mono
  intro p hp
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
  have hBound := (product_ambient_walk_bound (r : ℕ) r.pos p.1 p.2
    ((mem_boolean _ _).mp hu).1 ((mem_boolean _ _).mp hv).1).1
  exact_mod_cast hBound

/-- A bounded positive walk excess has mean at most its bound times its nonnegative-event mass. -/
theorem integral_boolean_positive_excess_le (n : ℕ) (i r : ℕ+) {K : ℝ} (hK : 0 ≤ K)
    (hBound : ∀ p ∈ (boolean n).product (boolean n),
      (recordWalk p.1 p.2 i : ℝ) - recordWalk p.1 p.2 r ≤ K) :
    (∫ p, max ((recordWalk p.1 p.2 i : ℝ) - recordWalk p.1 p.2 r) 0 ∂pairLaw (boolean n)) ≤
      K * (pairLaw (boolean n)).real
        {p | (recordWalk p.1 p.2 r : ℝ) ≤ recordWalk p.1 p.2 i} := by
  calc
    _ ≤ ∫ p, {q : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ |
        (recordWalk q.1 q.2 r : ℝ) ≤ recordWalk q.1 q.2 i}.indicator (fun _ => K) p
        ∂pairLaw (boolean n) := by
      apply integral_uniform_finset_mono
      intro p hp
      by_cases h : (recordWalk p.1 p.2 r : ℝ) ≤ recordWalk p.1 p.2 i
      · simp only [Set.indicator, Set.mem_ofPred_eq, ite_eq_left h]
        exact max_le (hBound p hp) hK
      · simp only [Set.indicator, Set.mem_ofPred_eq, ite_eq_right h]
        rw [max_eq_right (by linarith)]
    _ = _ := by
      rw [integral_indicator_const K
        (measurableSet_le (measurable_of_countable _) (measurable_of_countable _)),
        smul_eq_mul, mul_comm]

end RecordStability
