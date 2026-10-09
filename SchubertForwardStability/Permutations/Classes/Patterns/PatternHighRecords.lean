import SchubertForwardStability.Permutations.Classes.Patterns.PatternHighJoin
import SchubertForwardStability.Permutations.Statistics.Records

/-! # Records and unique factors in a higher-left maximum join

The records of `joinHigh a b u v` in size `a+b+1` are the records of `u` together with the
maximum position `a+1`, and the two factors are determined by the join.
-/

namespace PermutationPattern

open FinitaryPerm
open scoped Classical

/-- Records before a higher-left maximum are the left factor's records. -/
theorem joinHigh_isRecord_left (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hv : IsSupported b v) (i : ℕ+) (hi : (i : ℕ) ≤ a) :
    IsRecord (joinHigh a b u v) i ↔ IsRecord u i := by
  constructor <;> intro h j hj
  · have hjBound : (j : ℕ) ≤ a := by
      change (j : ℕ) < (i : ℕ) at hj
      omega
    have hx := h j hj
    rw [joinHigh_apply_left a b u v hv j hjBound,
      joinHigh_apply_left a b u v hv i hi] at hx
    change b + (u j : ℕ) < b + (u i : ℕ) at hx
    change (u j : ℕ) < (u i : ℕ)
    omega
  · have hjBound : (j : ℕ) ≤ a := by
      change (j : ℕ) < (i : ℕ) at hj
      omega
    rw [joinHigh_apply_left a b u v hv j hjBound,
      joinHigh_apply_left a b u v hv i hi]
    have hx := h j hj
    change (u j : ℕ) < (u i : ℕ) at hx
    change b + (u j : ℕ) < b + (u i : ℕ)
    omega

/-- The maximum position is a record of a higher-left join. -/
theorem joinHigh_isRecord_max (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (hv : IsSupported b v) :
    IsRecord (joinHigh a b u v) a.succPNat := by
  intro i hi
  have hiBound : (i : ℕ) ≤ a := by
    change (i : ℕ) < a + 1 at hi
    omega
  rw [joinHigh_apply_left a b u v hv i hiBound, joinHigh_apply_max a b u v hu hv]
  have hValue := (hu.apply_le_iff i).mpr hiBound
  change b + (u i : ℕ) < a + b + 1
  omega

/-- No bounded position after the new maximum is a higher-left joined record. -/
theorem joinHigh_notRecord_right (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (hv : IsSupported b v) (j : ℕ+)
    (hj : a + 1 < (j : ℕ)) (hn : (j : ℕ) ≤ a + b + 1) :
    ¬IsRecord (joinHigh a b u v) j := by
  intro hRecord
  have h := hRecord a.succPNat hj
  rw [joinHigh_apply_max a b u v hu hv] at h
  have hBound := ((joinHigh_supported a b u v hu hv).apply_le_iff j).mpr hn
  change a + b + 1 < (joinHigh a b u v j : ℕ) at h
  omega

/-- The higher-left record set inserts only the maximum position into the left records. -/
theorem joinHigh_recordSet (a b : ℕ) (u v : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (hv : IsSupported b v) :
    recordSet (a + b + 1) (joinHigh a b u v) = insert a.succPNat (recordSet a u) := by
  ext j
  simp only [mem_recordSet, Finset.mem_insert]
  constructor
  · rintro ⟨hj, hRecord⟩
    by_cases he : j = a.succPNat
    · exact Or.inl he
    · have hNe : (j : ℕ) ≠ a + 1 := fun h => he (PNat.eq h)
      have hLeft : (j : ℕ) ≤ a := by
        by_contra hn
        exact (joinHigh_notRecord_right a b u v hu hv j (by omega) hj) hRecord
      exact Or.inr ⟨hLeft, (joinHigh_isRecord_left a b u v hv j hLeft).mp hRecord⟩
  · rintro (he | ⟨hj, hRecord⟩)
    · subst j
      exact ⟨by change a + 1 ≤ a + b + 1; omega, joinHigh_isRecord_max a b u v hu hv⟩
    · exact ⟨by omega, (joinHigh_isRecord_left a b u v hv j hj).mpr hRecord⟩

/-- The two bounded factors of a higher-left join are unique. -/
theorem joinHigh_factors_eq (a b : ℕ) (u v u' v' : FinitaryPerm ℕ+)
    (hu : IsSupported a u) (hv : IsSupported b v)
    (hu' : IsSupported a u') (hv' : IsSupported b v')
    (h : joinHigh a b u v = joinHigh a b u' v') : u = u' ∧ v = v' := by
  constructor
  · apply ext
    intro i
    by_cases hi : (i : ℕ) ≤ a
    · have hx := congrArg (fun w : FinitaryPerm ℕ+ => w i) h
      rw [joinHigh_apply_left a b u v hv i hi, joinHigh_apply_left a b u' v' hv' i hi] at hx
      exact (shiftPosition b).injective hx
    · rw [hu i (by omega), hu' i (by omega)]
  · apply ext
    intro t
    by_cases ht : (t : ℕ) ≤ b
    · have hx := congrArg (fun w : FinitaryPerm ℕ+ => w (shiftPosition (a + 1) t)) h
      rwa [joinHigh_apply_right a b u v t ht, joinHigh_apply_right a b u' v' t ht] at hx
    · rw [hv t (by omega), hv' t (by omega)]

end PermutationPattern
