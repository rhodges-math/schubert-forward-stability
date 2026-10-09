import SchubertForwardStability.Paper.Uniform.Excess
import Mathlib.NumberTheory.ZetaValues

/-! # Sharp reciprocal-square bounds for ambient overshoots

Let `Y_i = Λ_i(u) + Λ_i(v) + i - 1` be the record walk. For independent uniform `u, v` in
`S_n` with `n >= 1`, the mean ambient overshoot `E[max_{i <= n+1} Y_i - Y_2]` lies between
`0` and `π^2/6 - 1`.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

/-- Reciprocal-square sums over a positive finite interval are at most the Basel sum. -/
theorem sum_reciprocalSquares_le_basel (n : ℕ) :
    (∑ j ∈ Finset.Icc (1 : ℕ) n, 1 / ((j : ℝ) ^ 2)) ≤ Real.pi ^ 2 / 6 :=
  sum_le_hasSum _ (fun _ _ => by positivity) hasSum_zeta_two

/-- The reciprocal-square tail starting at two is at most the Basel sum minus one. -/
theorem sum_reciprocalSquares_tail_le (n : ℕ) :
    (∑ j ∈ Finset.Icc (2 : ℕ) n, 1 / ((j : ℝ) ^ 2)) ≤ Real.pi ^ 2 / 6 - 1 := by
  have hbase : 1 ≤ Real.pi ^ 2 / 6 := by
    simpa using sum_reciprocalSquares_le_basel 1
  by_cases hn : 1 ≤ n
  · have hs : Finset.Icc (1 : ℕ) n = insert 1 (Finset.Icc 2 n) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h := sum_reciprocalSquares_le_basel n
    rw [hs, Finset.sum_insert (by simp)] at h
    norm_num at h
    simp only [one_div] at *
    linarith
  · have he : n = 0 := by omega
    subst n
    simp only [Finset.Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 2), Finset.sum_empty]
    linarith

/-- Starting the ambient maximum at two does not remove a maximizing walk value. -/
theorem recordWalkMaxAt_eq_maxFrom_two {n : ℕ} (hn : 1 ≤ n)
    (u v : FinitaryPerm ℕ+) : recordWalkMaxAt n u v = recordWalkMaxFrom n 2 u v := by
  have hs := recordWalkStep_eq u v 1
  rw [nonRecordIndicator_eq_zero (isRecord_first u),
    nonRecordIndicator_eq_zero (isRecord_first v)] at hs
  change recordWalk u v 2 - recordWalk u v 1 = 1 - 0 - 0 at hs
  apply le_antisymm
  · obtain ⟨j, hj, he⟩ := exists_recordWalk_eq_maxAt n u v
    rw [←he]
    by_cases hij : (2 : ℕ+) ≤ j
    · exact recordWalk_le_maxFrom 2 u v hij hj
    · have hj1 : j = 1 := by
        apply PNat.eq
        change (j : ℕ) = 1
        have hp := PNat.pos j
        change ¬(2 : ℕ) ≤ (j : ℕ) at hij
        omega
      subst j
      exact (by omega : recordWalk u v 1 ≤ recordWalk u v 2).trans
        (recordWalk_le_maxFrom 2 u v le_rfl (by change 2 ≤ n + 1; omega))
  · obtain ⟨j, _, hj, he⟩ := exists_recordWalk_eq_maxFrom 2 u v
      (by change 2 ≤ n + 1; omega)
    rw [←he]
    exact recordWalk_le_maxAt u v hj

/-- At ambient size one the second walk value already is the whole maximum. -/
theorem recordWalkMaxAt_one_eq_second (u v : FinitaryPerm ℕ+) :
    recordWalkMaxAt 1 u v = recordWalk u v 2 := by
  rw [recordWalkMaxAt_eq_maxFrom_two (by rfl : 1 ≤ 1)]
  obtain ⟨j, hl, hr, he⟩ := exists_recordWalk_eq_maxFrom 2 u v (by norm_num : 2 ≤ 1 + 1)
  have hj : j = 2 := by
    apply PNat.eq
    change (j : ℕ) = 2
    change 2 ≤ (j : ℕ) at hl
    omega
  simpa only [hj] using he.symm

/-- Positive-size uniform ambient overshoots lie between zero and the sharp Basel tail. -/
theorem integral_uniform_ambient_bounds {n : ℕ} (hn : 1 ≤ n) :
    (∫ p, ((recordWalkMaxAt n p.1 p.2 - recordWalk p.1 p.2 2 : ℤ) : ℝ)
      ∂pairLaw (symmetricGroup n)) ∈ Set.Icc (0 : ℝ) (Real.pi ^ 2 / 6 - 1) := by
  constructor
  · apply integral_nonneg
    intro p
    change (0 : ℝ) ≤ ((recordWalkMaxAt n p.1 p.2 - recordWalk p.1 p.2 2 : ℤ) : ℝ)
    exact_mod_cast sub_nonneg.mpr (recordWalk_le_maxAt (n := n) (i := 2) p.1 p.2
      (by change 2 ≤ n + 1; omega))
  · by_cases hn2 : 2 ≤ n
    · have he : (fun p : FinitaryPerm ℕ+ × FinitaryPerm ℕ+ =>
          ((recordWalkMaxAt n p.1 p.2 - recordWalk p.1 p.2 2 : ℤ) : ℝ)) =
          (fun p => ((recordWalkMaxFrom n 2 p.1 p.2 - recordWalk p.1 p.2 2 : ℤ) : ℝ)) :=
        funext fun p => by rw [recordWalkMaxAt_eq_maxFrom_two hn]
      rw [he]
      exact (integral_uniform_overshoot n 2 hn2).trans (sum_reciprocalSquares_tail_le n)
    · have he : n = 1 := by omega
      subst n
      simp only [recordWalkMaxAt_one_eq_second, sub_self, Int.cast_zero, integral_zero]
      have hbase : 1 ≤ Real.pi ^ 2 / 6 := by
        simpa using sum_reciprocalSquares_le_basel 1
      linarith

end RecordStability
