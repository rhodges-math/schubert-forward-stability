import SchubertForwardStability.SchubertPolynomials.Stability.ShiftForward

/-! # Iterated insertion of initial fixed positions

Signed translations compose. Iterated insertion preserves transported
coordinates and gives the corresponding increase of nonidentity product
forward support. Extension of a reversed interval is the same insertion.
-/

namespace FinitaryPerm

/-- Two admissible signed translations compose by addition of their amounts. -/
theorem SignedShift.trans {k l : ℤ} {u v w : FinitaryPerm ℕ+}
    (h : SignedShift k u v) (h' : SignedShift l v w) : SignedShift (k + l) u w := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    by_cases hm : ((i : ℕ) : ℤ) + k ≤ 0
    · exact h.removed_fixed i hm
    · let j : ℕ+ := ⟨(((i : ℕ) : ℤ) + k).toNat, by omega⟩
      have hj : ((j : ℕ) : ℤ) = ((i : ℕ) : ℤ) + k := by dsimp [j]; omega
      have he := h'.removed_fixed j (by omega)
      have ht := h.translate i j hj
      rw [he] at ht
      apply PNat.eq
      omega
  · intro j hj
    by_cases hm : ((j : ℕ) : ℤ) ≤ l
    · exact h'.inserted_fixed j hm
    · let i : ℕ+ := ⟨(((j : ℕ) : ℤ) - l).toNat, by omega⟩
      have hi : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) - l := by dsimp [i]; omega
      have he := h.inserted_fixed i (by omega)
      have ht := h'.translate i j (by omega)
      rw [he] at ht
      apply PNat.eq
      omega
  · intro i j hij
    by_cases hm : ((i : ℕ) : ℤ) + k ≤ 0
    · rw [h.removed_fixed i hm, h'.inserted_fixed j (by omega)]
      exact hij
    · let a : ℕ+ := ⟨(((i : ℕ) : ℤ) + k).toNat, by omega⟩
      have ha : ((a : ℕ) : ℤ) = ((i : ℕ) : ℤ) + k := by dsimp [a]; omega
      have ht := h.translate i a ha
      have ht' := h'.translate a j (by omega)
      omega

/-- Insert a prescribed natural number of initial fixed positions. -/
def initialShift : ℕ → FinitaryPerm ℕ+ → FinitaryPerm ℕ+
  | 0, w => w
  | d + 1, w => shiftRight (initialShift d w)

/-- Zero insertion leaves the permutation unchanged. -/
@[simp] theorem initialShift_zero (w : FinitaryPerm ℕ+) : initialShift 0 w = w := rfl

/-- Successor insertion adds one more initial fixed position. -/
theorem initialShift_succ (d : ℕ) (w : FinitaryPerm ℕ+) :
    initialShift (d + 1) w = shiftRight (initialShift d w) := rfl

/-- Identity is unchanged by every natural insertion. -/
@[simp] theorem initialShift_one (d : ℕ) : initialShift d (1 : FinitaryPerm ℕ+) = 1 := by
  induction d with
  | zero => rfl
  | succ d hd => rw [initialShift_succ, hd, shiftRight_one]

/-- Natural insertion satisfies the intrinsic signed-translation relation. -/
theorem initialShift_signed (d : ℕ) (w : FinitaryPerm ℕ+) :
    SignedShift (d : ℤ) w (initialShift d w) := by
  induction d with
  | zero => exact SignedShift.zero w
  | succ d hd =>
    simpa only [Nat.cast_add, Nat.cast_one, initialShift_succ] using
      hd.trans (shiftRight_signed _)

/-- Insertion preserves and reflects identity. -/
theorem initialShift_eq_one_iff (d : ℕ) (w : FinitaryPerm ℕ+) :
    initialShift d w = 1 ↔ w = 1 := by
  constructor
  · intro h
    have hs := (initialShift_signed d w).symm
    rw [h] at hs
    exact hs.eq_one
  · rintro rfl
    exact initialShift_one d

/-- Natural insertion translates an ambient support bound by the same amount. -/
theorem IsSupported.initialShift {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (d : ℕ) : IsSupported (n + d) (initialShift d w) := by
  induction d with
  | zero => simpa only [Nat.add_zero, initialShift_zero] using hw
  | succ d hd => simpa only [Nat.add_assoc, initialShift_succ] using hd.shiftRight

/-- Extending a reversed interval by one fixed final position inserts one initial fixed position. -/
theorem conjugate_longest_succ {n : ℕ} {w : FinitaryPerm ℕ+} (hw : IsSupported n w) :
    longestElement (n + 1) * w * longestElement (n + 1) =
      shiftRight (longestElement n * w * longestElement n) := by
  have h := conjugate_longest_shiftRight hw.conjugate_longest
  rw [conjugate_longest_twice] at h
  calc
    _ = longestElement (n + 1) *
        (longestElement (n + 1) * shiftRight (longestElement n * w * longestElement n) *
          longestElement (n + 1)) * longestElement (n + 1) := by rw [h]
    _ = _ := conjugate_longest_twice _ _

/-- Extending a reversed interval inserts the difference in ambient sizes at the beginning. -/
theorem conjugate_longest_extend {n : ℕ} {w : FinitaryPerm ℕ+}
    (hw : IsSupported n w) (d : ℕ) :
    longestElement (n + d) * w * longestElement (n + d) =
      initialShift d (longestElement n * w * longestElement n) := by
  induction d with
  | zero => rfl
  | succ d hd =>
    rw [Nat.add_succ, conjugate_longest_succ (hw.mono (Nat.le_add_right _ _)),
      hd, initialShift_succ]

end FinitaryPerm

namespace SchubertPolynomial

open FinitaryPerm

/-- Simultaneous natural insertion preserves the three transported integer coordinates. -/
theorem structureConst_initialShift (d : ℕ) (u v w : FinitaryPerm ℕ+) :
    structureConst (initialShift d u) (initialShift d v) (initialShift d w) =
      structureConst u v w := by
  induction d with
  | zero => rfl
  | succ d hd => rw [initialShift_succ, initialShift_succ, initialShift_succ,
      structureConst_shiftRight, hd]

/-- Natural insertion increases nonidentity product forward support by the insertion amount. -/
theorem productForward_initialShift (d : ℕ) (u v : FinitaryPerm ℕ+)
    (h : u ≠ 1 ∨ v ≠ 1) :
    productForwardStability (initialShift d u) (initialShift d v) =
      productForwardStability u v + d := by
  induction d with
  | zero => rfl
  | succ d hd =>
    have hn : initialShift d u ≠ 1 ∨ initialShift d v ≠ 1 := by
      exact h.elim (fun hu => Or.inl (fun he => hu ((initialShift_eq_one_iff d u).mp he)))
        (fun hv => Or.inr (fun he => hv ((initialShift_eq_one_iff d v).mp he)))
    rw [initialShift_succ, initialShift_succ, productForward_shiftRight _ _ hn, hd]
    omega

end SchubertPolynomial
