import SchubertForwardStability.Permutations.Classes.Patterns.PatternJoin

/-! # Unique factor recovery for maximum joins

Two lower-left maximum joins of supported factors are equal only when their factors are
equal.
-/

namespace PermutationPattern

open FinitaryPerm

/-- Two supported maximum joins agree only when both of their factors agree. -/
theorem joinLow_factors_eq (a b : ℕ) (u v u' v' : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (hv : IsSupported b v)
    (hu' : IsSupported a u') (hv' : IsSupported b v')
    (h : joinLow a b u v = joinLow a b u' v') : u = u' ∧ v = v' := by
  constructor
  · apply FinitaryPerm.ext
    intro i
    by_cases hi : (i : ℕ) ≤ a
    · have he := congrArg (fun w : FinitaryPerm ℕ+ => w i) h
      rwa [joinLow_apply_left a b u v i hi, joinLow_apply_left a b u' v' i hi] at he
    · rw [hu i (lt_of_not_ge hi), hu' i (lt_of_not_ge hi)]
  · apply FinitaryPerm.ext
    intro t
    by_cases ht : (t : ℕ) ≤ b
    · have he := congrArg (fun w : FinitaryPerm ℕ+ => w (shiftPosition (a + 1) t)) h
      rw [joinLow_apply_right a b u v hu t ht,
        joinLow_apply_right a b u' v' hu' t ht] at he
      exact (shiftPosition a).injective he
    · rw [hv t (lt_of_not_ge ht), hv' t (lt_of_not_ge ht)]

end PermutationPattern
