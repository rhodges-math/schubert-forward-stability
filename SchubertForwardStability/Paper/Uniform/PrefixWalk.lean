import SchubertForwardStability.Permutations.Random.RecordPrefix
import SchubertForwardStability.Paper.Uniform.AmbientBounds

/-! # Monotone uniform overshoot expectations from finite prefix coupling

Coupling a uniform permutation of `S_N` with its record prefix in `S_n` preserves the walk
increments from the second position. Hence the mean ambient overshoot of the record walk is
nondecreasing in the ambient size `n >= 1`.
-/

namespace RecordStability

open FinitaryPerm MeasureTheory ProbabilityTheory
open scoped Classical

/-- Prefix coupling preserves every walk displacement from the second position. -/
theorem prefix_walk_displacement (n : ℕ) (u v : FinitaryPerm ℕ+) (k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    recordWalk (recordPrefix n u) (recordPrefix n v) k.succPNat -
        recordWalk (recordPrefix n u) (recordPrefix n v) 2 =
      recordWalk u v k.succPNat - recordWalk u v 2 := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst k
      simp only [show (1 : ℕ).succPNat = 2 from rfl, sub_self]
    · have hprev := ih (by omega) (by omega)
      have he : (k + 1).succPNat = k.succPNat + 1 := by
        apply PNat.eq
        rfl
      have hs : recordWalkStep (recordPrefix n u) (recordPrefix n v) k.succPNat =
          recordWalkStep u v k.succPNat := by
        rw [recordWalkStep_eq, recordWalkStep_eq,
          nonRecordIndicator_recordPrefix u _ (by change k + 1 ≤ n; omega),
          nonRecordIndicator_recordPrefix v _ (by change k + 1 ≤ n; omega)]
      rw [he]
      unfold recordWalkStep at hs
      omega

/-- A smaller decoded ambient overshoot is bounded by the original larger overshoot. -/
theorem prefix_ambient_overshoot_le {n N : ℕ} (hn : 1 ≤ n) (hN : n ≤ N)
    (u v : FinitaryPerm ℕ+) :
    recordWalkMaxAt n (recordPrefix n u) (recordPrefix n v) -
        recordWalk (recordPrefix n u) (recordPrefix n v) 2 ≤
      recordWalkMaxAt N u v - recordWalk u v 2 := by
  rw [recordWalkMaxAt_eq_maxFrom_two hn]
  obtain ⟨j, hj, hjn, he⟩ := exists_recordWalk_eq_maxFrom 2
    (recordPrefix n u) (recordPrefix n v) (by change 2 ≤ n + 1; omega)
  rw [←he]
  let k := (j : ℕ) - 1
  have hk : 1 ≤ k := by change 2 ≤ (j : ℕ) at hj; dsimp [k]; omega
  have hkn : k ≤ n := by dsimp [k]; omega
  have he : k.succPNat = j := by
    apply PNat.eq
    change (j : ℕ) - 1 + 1 = (j : ℕ)
    have := PNat.pos j
    omega
  have hd := prefix_walk_displacement n u v k hk hkn
  rw [he] at hd
  rw [hd]
  exact sub_le_sub_right (recordWalk_le_maxAt u v (hjn.trans (Nat.add_le_add_right hN 1))) _

/-- Uniform ambient overshoot expectations are monotone over positive ambient sizes. -/
theorem integral_uniform_ambient_monotone : MonotoneOn
    (fun n : ℕ => ∫ p,
      ((recordWalkMaxAt n p.1 p.2 - recordWalk p.1 p.2 2 : ℤ) : ℝ)
        ∂pairLaw (symmetricGroup n)) (Set.Ici 1) := by
  intro m hm n _ hmn
  dsimp only
  rw [←map_pair_recordPrefix hmn,
    integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
  apply integral_uniform_finset_mono
  intro p _
  dsimp only [Prod.map]
  exact_mod_cast prefix_ambient_overshoot_le hm hmn p.1 p.2

end RecordStability
