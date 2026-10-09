import SchubertForwardStability.SchubertPolynomials.Stability.Recurrence.TransitionTerms

/-! # Schubert transition at an increasing-tail pivot

## Main results

The Schubert polynomial at a pivot is its pivot-variable multiple plus the finite
positive sum over gap-free left covers. The identity holds over every commutative ring.
-/

namespace SchubertPolynomial

open FinitaryPerm
open scoped Classical

variable {R : Type*} [CommRing R]

private theorem swap_restore (v : FinitaryPerm ℕ+) (a b : ℕ+) :
    (v * swap a b) * swap a b = v := by
  have hs : (swap a b : FinitaryPerm ℕ+) * swap a b = 1 := by
    simpa only [swap_inv] using mul_inv_cancel (swap a b)
  rw [mul_assoc, hs, mul_one]

private theorem functional_X_cover (j : ℕ+) (v z : FinitaryPerm ℕ+) (a b : ℕ+)
    (hab : a < b) (he : z = v * swap a b) (hl : z.length = v.length + 1) :
    schubertFunctional R z (MvPolynomial.X j * schubert R v) =
      (if a = j then 1 else 0) - (if b = j then 1 else 0) := by
  have hb : z * swap a b = v := by rw [he]; exact swap_restore v a b
  have hx := schubertFunctional_linear_cover (Finsupp.single j (1 : R)) z a b hab
    (by rw [hb]; omega)
  rw [hb, linearForm_single, one_smul] at hx
  simpa only [Finsupp.single_apply, eq_comm] using hx

private theorem cover_coordinates {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) (z : FinitaryPerm ℕ+) (a b : ℕ+) (hab : a < b)
    (he : z = (w * swap r s) * swap a b)
    (hl : z.length = (w * swap r s).length + 1) :
    schubertFunctional R z (MvPolynomial.X r * schubert R (w * swap r s)) +
      schubertFunctional R z (transitionSum R (w * swap r s) r) =
        if z = w then 1 else 0 := by
  have hx := functional_X_cover (R := R) r (w * swap r s) z a b hab he hl
  have hw := swap_restore w r s
  by_cases ha : a = r
  · subst a
    have hb := (h.swapped_cover_iff hab).mp (by simpa only [he] using hl)
    subst b
    have hz : z = w := he.trans hw
    rw [hz] at hx ⊢
    rw [hx, transitionSum_functional_pivot h]
    simp only [ite_true, ite_eq_right h.start_lt.ne', sub_zero, add_zero]
  · by_cases hb : b = r
    · subst b
      have hq : a ∈ transitionPositions (w * swap r s) r := by
        apply (mem_transitionPositions _ _ _).mpr
        exact (length_exchange_cover_iff hab).mp (by simpa only [he] using hl)
      have hs : schubertFunctional R z (transitionSum R (w * swap r s) r) = 1 := by
        rw [he]
        exact transitionSum_functional_at hq
      have hn : z ≠ w := by
        intro hz
        have ht := swap_ordered_injective hab h.start_lt
          (mul_left_cancel (he.symm.trans (hz.trans hw.symm)))
        exact ha ht.1
      rw [hx, hs, ite_eq_right hn, ite_eq_right ha]
      simp only [ite_true, zero_sub, neg_add_cancel]
    · have hs : schubertFunctional R z (transitionSum R (w * swap r s) r) = 0 := by
        apply transitionSum_functional_outside
        intro q hq hz
        have ht := swap_ordered_injective hab
          ((mem_transitionPositions _ _ _).mp hq).left_lt
          (mul_left_cancel (he.symm.trans hz))
        exact hb ht.2
      have hn : z ≠ w := by
        intro hz
        have ht := swap_ordered_injective hab h.start_lt
          (mul_left_cancel (he.symm.trans (hz.trans hw.symm)))
        exact ha ht.1
      rw [hx, hs, ite_eq_right hn, ite_eq_right ha, ite_eq_right hb]
      simp only [sub_self, add_zero]

private theorem outside_coordinates {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) (z : FinitaryPerm ℕ+)
    (hl : z.length = (w * swap r s).length + 1)
    (hn : ∀ a b : ℕ+, a < b → z ≠ (w * swap r s) * swap a b) :
    schubertFunctional R z (MvPolynomial.X r * schubert R (w * swap r s)) +
      schubertFunctional R z (transitionSum R (w * swap r s) r) =
        if z = w then 1 else 0 := by
  have hx := schubertFunctional_linear_outside (Finsupp.single r (1 : R))
    (w * swap r s) z hl (by
      intro a b hab he
      apply hn a b hab
      exact (swap_restore z a b).symm.trans
        (congrArg (fun p : FinitaryPerm ℕ+ => p * swap a b) he.symm))
  rw [linearForm_single, one_smul] at hx
  have hs : schubertFunctional R z (transitionSum R (w * swap r s) r) = 0 := by
    apply transitionSum_functional_outside
    intro q hq
    exact hn q r ((mem_transitionPositions _ _ _).mp hq).left_lt
  have hz : z ≠ w := by
    intro he
    exact hn r s h.start_lt (he.trans (swap_restore w r s).symm)
  rw [hx, hs, ite_eq_right hz, add_zero]

/-- The finite positive Schubert transition formula at an increasing-tail pivot. -/
theorem schubert_transition {w : FinitaryPerm ℕ+} {r s : ℕ+}
    (h : IncreasingTailPivot w r s) :
    schubert R w = MvPolynomial.X r * schubert R (w * swap r s) +
      transitionSum R (w * swap r s) r := by
  apply (schubertBasis R).repr.injective
  apply Finsupp.ext
  intro z
  rw [schubertBasis_repr, schubertBasis_repr, map_add, schubertFunctional_schubert]
  by_cases hl : z.length = (w * swap r s).length + 1
  · by_cases he : ∃ a b : ℕ+, a < b ∧ z = (w * swap r s) * swap a b
    · obtain ⟨a, b, hab, hz⟩ := he
      exact (cover_coordinates (R := R) h z a b hab hz hl).symm
    · exact (outside_coordinates (R := R) h z hl (by
        intro a b hab hz
        exact he ⟨a, b, hab, hz⟩)).symm
  · have hp := (MvPolynomial.isHomogeneous_X R r).mul
      (schubert_isHomogeneous (R := R) (w * swap r s))
    have hx := schubertFunctional_off_degree z hp (by simpa only [Nat.add_comm] using hl)
    have hs := schubertFunctional_off_degree (R := R) z
      (transitionSum_isHomogeneous (R := R) (w * swap r s) r) hl
    have hn : z ≠ w := by
      intro hz
      exact hl (hz ▸ h.swapped_length)
    rw [hx, hs, ite_eq_right hn, add_zero]

end SchubertPolynomial
