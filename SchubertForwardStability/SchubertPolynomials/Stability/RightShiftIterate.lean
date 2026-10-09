import SchubertForwardStability.SchubertPolynomials.Stability.RightShift

/-! # Iterated right shifts

## Main results

* `exists_shiftRight_eq`: a finitary permutation fixing the first position is a right shift.
* `iterate_shiftRight_apply_le`, `iterate_shiftRight_apply_add`: the action of the `k`-fold
  right shift, which fixes the first `k` positions and translates the others by `k`.
* `signedShift_iterate_shiftRight`: the `k`-fold right shift is the signed shift of amount `k`.
-/

namespace FinitaryPerm

private def tailEquiv : ℕ+ ≃ {j : ℕ+ // 1 < j} where
  toFun i := ⟨i + 1, by
    change 1 < (i : ℕ) + 1
    have hi := i.pos
    omega⟩
  invFun j := ⟨(j.val : ℕ) - 1, by
    have hj : 1 < (j.val : ℕ) := j.property
    omega⟩
  left_inv i := by
    apply PNat.eq
    change (i : ℕ) + 1 - 1 = (i : ℕ)
    omega
  right_inv j := by
    apply Subtype.ext
    apply PNat.eq
    change (j.val : ℕ) - 1 + 1 = (j.val : ℕ)
    have hj : 1 < (j.val : ℕ) := j.property
    omega

private theorem one_lt_iff_ne_one (j : ℕ+) : 1 < j ↔ j ≠ 1 := by
  constructor
  · exact fun h he => (lt_irrefl (1 : ℕ+)) (he ▸ h)
  · intro h
    have hj : (j : ℕ) ≠ 1 := fun he => h (PNat.eq he)
    have hp := j.pos
    change 1 < (j : ℕ)
    omega

/-- A finitary permutation fixing the first position is the right shift of a finitary
permutation. -/
theorem exists_shiftRight_eq {w : FinitaryPerm ℕ+} (hw : w 1 = 1) :
    ∃ w₀ : FinitaryPerm ℕ+, shiftRight w₀ = w := by
  have hmem : ∀ j : ℕ+, 1 < j ↔ 1 < w j := by
    intro j
    rw [one_lt_iff_ne_one, one_lt_iff_ne_one]
    constructor
    · intro hj he
      exact hj (w.injective (he.trans hw.symm))
    · intro hj he
      subst j
      exact hj hw
  let σ : Equiv.Perm {j : ℕ+ // 1 < j} := w.val.subtypePerm (fun j => (hmem j).symm)
  let τ : Equiv.Perm ℕ+ := tailEquiv.symm.permCongr σ
  have hτ (i : ℕ+) : τ i + 1 = w (i + 1) := by
    have h := tailEquiv.apply_symm_apply (σ (tailEquiv i))
    have hv := congrArg Subtype.val h
    change ((τ i : ℕ+) + 1 : ℕ+) = (σ (tailEquiv i)).val at hv
    rw [hv]
    rfl
  have hfin : {i | τ i ≠ i}.Finite := by
    apply (w.finite_movedSet.preimage (f := fun i : ℕ+ => i + 1)
      (fun a _ b _ hab => add_right_cancel hab)).subset
    intro i hi he
    apply hi
    have h := hτ i
    rw [he] at h
    exact add_right_cancel h
  refine ⟨ofPerm τ hfin, ?_⟩
  apply ext
  intro j
  by_cases hj : j = 1
  · subst j
    rw [shiftRight_apply_one, hw]
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ+, i + 1 = j := by
      refine ⟨(tailEquiv.symm ⟨j, (one_lt_iff_ne_one j).mpr hj⟩), ?_⟩
      exact congrArg Subtype.val (tailEquiv.apply_symm_apply ⟨j, (one_lt_iff_ne_one j).mpr hj⟩)
    rw [shiftRight_apply_add_one, ofPerm_apply, hτ]

private theorem exists_add_one_eq {j : ℕ+} (hj : j ≠ 1) : ∃ i : ℕ+, i + 1 = j :=
  ⟨tailEquiv.symm ⟨j, (one_lt_iff_ne_one j).mpr hj⟩,
    congrArg Subtype.val (tailEquiv.apply_symm_apply ⟨j, (one_lt_iff_ne_one j).mpr hj⟩)⟩

/-- The `k`-fold right shift fixes every position up to `k`. -/
theorem iterate_shiftRight_apply_le (w : FinitaryPerm ℕ+) (k : ℕ) (j : ℕ+) (hj : (j : ℕ) ≤ k) :
    shiftRight^[k] w j = j := by
  induction k generalizing j with
  | zero => have := j.pos; omega
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    by_cases h1 : j = 1
    · subst j
      exact shiftRight_apply_one _
    · obtain ⟨i, rfl⟩ := exists_add_one_eq h1
      rw [shiftRight_apply_add_one, ih i (by rw [PNat.add_coe] at hj; simp at hj; omega)]

/-- The `k`-fold right shift translates every position and its value by `k`. -/
theorem iterate_shiftRight_apply_of_eq_add (w : FinitaryPerm ℕ+) (k : ℕ) {i j : ℕ+}
    (hij : (j : ℕ) = (i : ℕ) + k) : ((shiftRight^[k] w j : ℕ+) : ℕ) = (w i : ℕ) + k := by
  induction k generalizing j with
  | zero =>
    have he : j = i := PNat.eq (by simpa using hij)
    simp [he]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hj1 : j ≠ 1 := by
      intro he
      subst j
      have := i.pos
      simp at hij
      omega
    obtain ⟨j', rfl⟩ := exists_add_one_eq hj1
    rw [shiftRight_apply_add_one, PNat.add_coe,
      ih (by rw [PNat.add_coe] at hij; simp at hij; omega)]
    simp only [PNat.one_coe]
    omega

/-- The `k`-fold right shift is the signed shift of amount `k`. -/
theorem signedShift_iterate_shiftRight (w : FinitaryPerm ℕ+) (k : ℕ) :
    SignedShift k w (shiftRight^[k] w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have := i.pos
    omega
  · intro j hj
    exact iterate_shiftRight_apply_le w k j (by exact_mod_cast hj)
  · intro i j hij
    have h := iterate_shiftRight_apply_of_eq_add w k (i := i) (j := j) (by omega)
    omega

/-- A permutation is the signed shift of amount `k ≥ 0` of `w` exactly when it is the `k`-fold
right shift of `w`. -/
theorem signedShift_natCast_iff (w v : FinitaryPerm ℕ+) (k : ℕ) :
    SignedShift k w v ↔ v = shiftRight^[k] w :=
  ⟨fun h => h.unique (signedShift_iterate_shiftRight w k), fun h => h ▸
    signedShift_iterate_shiftRight w k⟩

end FinitaryPerm
