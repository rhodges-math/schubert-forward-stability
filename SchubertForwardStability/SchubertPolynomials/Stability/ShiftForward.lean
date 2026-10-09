import SchubertForwardStability.SchubertPolynomials.Stability.ShiftSuffix

/-! # Forward support after an initial fixed position

The suffix maximum characterizes product forward support without a chosen
cutoff. Suffix translation then increases the product support bound by one
for nonidentity pairs; the two-identity pair retains its positive floor.
-/

namespace FinitaryPerm

open scoped Classical

/-- The paired suffix maximum is bounded exactly when every positive candidate is bounded. -/
theorem pairSuffixBound_le_iff_all (u v : FinitaryPerm ℕ+) (n : ℕ) :
    pairSuffixBound u v ≤ n ↔ 1 ≤ n ∧ ∀ i : ℕ+,
      0 < u.suffixNonRecordCount i + v.suffixNonRecordCount i →
        (i : ℕ) + u.suffixNonRecordCount i + v.suffixNonRecordCount i ≤ n := by
  constructor
  · intro h
    refine ⟨(one_le_pairSuffixBound u v).trans h, ?_⟩
    intro i hi
    have hb : (i : ℕ) ≤ max u.forwardStability v.forwardStability := by
      by_contra hn
      have hu := suffixNonRecordCount_eq_zero u ((le_max_left _ _).trans (le_of_not_ge hn))
      have hv := suffixNonRecordCount_eq_zero v ((le_max_right _ _).trans (le_of_not_ge hn))
      rw [hu, hv] at hi
      exact (Nat.lt_irrefl 0) hi
    exact (suffix_candidate_le hb hi).trans h
  · rintro ⟨hn, h⟩
    apply max_le hn
    apply Finset.sup_le
    intro i _
    split_ifs with hz
    · exact Nat.zero_le _
    · exact h i (Nat.pos_of_ne_zero hz)

private theorem eq_one_of_forward_le_one (w : FinitaryPerm ℕ+) (hw : w.forwardStability ≤ 1) :
    w = 1 := by
  have hs := (forwardStability_le_iff w (by decide : 1 ≤ 1)).mp hw
  apply ext
  intro i
  rw [one_apply]
  by_cases hi : i = 1
  · subst i
    apply PNat.eq
    have hle := (hs.apply_le_iff 1).mpr (le_rfl : (1 : ℕ+) ≤ 1)
    have hp := (w 1).pos
    change (w 1 : ℕ) = 1
    change (w 1 : ℕ) ≤ 1 at hle
    omega
  · apply hs i
    have hp := i.pos
    have hn : (i : ℕ) ≠ 1 := fun he => hi (PNat.eq he)
    omega

end FinitaryPerm

namespace SchubertPolynomial

open FinitaryPerm

/-- Product forward support is characterized by all positive suffix candidates. -/
theorem productForward_le_iff_suffix (u v : FinitaryPerm ℕ+) (n : ℕ) :
    productForwardStability u v ≤ n ↔ 1 ≤ n ∧ ∀ i : ℕ+,
      0 < u.suffixNonRecordCount i + v.suffixNonRecordCount i →
        (i : ℕ) + u.suffixNonRecordCount i + v.suffixNonRecordCount i ≤ n := by
  rw [productForwardStability_eq_suffixBound, pairSuffixBound_le_iff_all]

/-- The product forward bound contains the forward bound of its left input. -/
theorem forward_input_le_product_left (u v : FinitaryPerm ℕ+) :
    u.forwardStability ≤ productForwardStability u v := by
  rw [productForwardStability_eq_suffixBound]
  exact forward_le_pairSuffixBound_left u v

/-- The product forward bound contains the forward bound of its right input. -/
theorem forward_input_le_product_right (u v : FinitaryPerm ℕ+) :
    v.forwardStability ≤ productForwardStability u v := by
  rw [productForwardStability_comm]
  exact forward_input_le_product_left v u

/-- A pair with a nonidentity input has product forward stability greater than one. -/
theorem one_lt_productForward (u v : FinitaryPerm ℕ+) (h : u ≠ 1 ∨ v ≠ 1) :
    1 < productForwardStability u v := by
  rcases h with hu | hv
  · have hl : 1 < u.forwardStability :=
      lt_of_not_ge fun he => hu (FinitaryPerm.eq_one_of_forward_le_one u he)
    exact hl.trans_le (forward_input_le_product_left u v)
  · have hl : 1 < v.forwardStability :=
      lt_of_not_ge fun he => hv (FinitaryPerm.eq_one_of_forward_le_one v he)
    exact hl.trans_le (forward_input_le_product_right u v)

/-- Inserting an initial fixed position increases nonidentity product forward support by one. -/
theorem productForward_shiftRight (u v : FinitaryPerm ℕ+) (h : u ≠ 1 ∨ v ≠ 1) :
    productForwardStability (shiftRight u) (shiftRight v) = productForwardStability u v + 1 := by
  have hF := one_lt_productForward u v h
  have hc := (productForward_le_iff_suffix u v (productForwardStability u v)).mp le_rfl
  apply le_antisymm
  · apply (productForward_le_iff_suffix _ _ _).mpr
    refine ⟨by omega, ?_⟩
    intro j hj
    by_cases he : j = 1
    · subst j
      rw [suffixNonRecordCount_shiftRight_first, suffixNonRecordCount_shiftRight_first] at hj ⊢
      exact (hc.2 1 hj).trans (Nat.le_succ _)
    · have hp : 0 < (j : ℕ) - 1 := by
        have hjp := j.pos
        have hn : (j : ℕ) ≠ 1 := fun hh => he (PNat.eq hh)
        omega
      let i : ℕ+ := ⟨(j : ℕ) - 1, hp⟩
      have hi : i + 1 = j := PNat.eq (by
        change (j : ℕ) - 1 + 1 = (j : ℕ)
        omega)
      rw [←hi, suffixNonRecordCount_shiftRight_succ,
        suffixNonRecordCount_shiftRight_succ] at hj ⊢
      have hb := hc.2 i hj
      change (i : ℕ) + 1 + u.suffixNonRecordCount i + v.suffixNonRecordCount i ≤ _
      omega
  · have hl : productForwardStability u v <
        productForwardStability (shiftRight u) (shiftRight v) := by
      by_contra hn
      have hs := (productForward_le_iff_suffix (shiftRight u) (shiftRight v)
        (productForwardStability u v)).mp (le_of_not_gt hn)
      have hold : productForwardStability u v ≤ productForwardStability u v - 1 := by
        apply (productForward_le_iff_suffix u v _).mpr
        refine ⟨by omega, ?_⟩
        intro i hi
        have hp : 0 < (shiftRight u).suffixNonRecordCount (i + 1) +
            (shiftRight v).suffixNonRecordCount (i + 1) := by
          rw [suffixNonRecordCount_shiftRight_succ, suffixNonRecordCount_shiftRight_succ]
          exact hi
        have hb := hs.2 (i + 1) hp
        rw [suffixNonRecordCount_shiftRight_succ, suffixNonRecordCount_shiftRight_succ] at hb
        change (i : ℕ) + 1 + u.suffixNonRecordCount i + v.suffixNonRecordCount i ≤ _ at hb
        omega
      omega
    exact Nat.succ_le_of_lt hl

end SchubertPolynomial
