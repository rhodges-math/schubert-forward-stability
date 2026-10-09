import SchubertForwardStability.SchubertPolynomials.Stability.ShiftRelation

/-! # Inserting an initial fixed position

## Main definitions

* `shiftRight`: fix the first position and translate every original position and value by one.

## Main results

Right shift preserves identity and multiplication, is injective, and is a signed shift
of amount one. Its action is explicit at the first position and at every successor.

## Implementation notes

The successor-tail equivalence transports a permutation to the positions after one.
Extension by identity preserves finite moved support.
-/

namespace FinitaryPerm

private def shiftTailEquiv : ℕ+ ≃ {j : ℕ+ // 1 < j} where
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

private def shiftPerm (w : FinitaryPerm ℕ+) : Equiv.Perm ℕ+ :=
  Equiv.Perm.ofSubtype (shiftTailEquiv.permCongr w.val)

private theorem shiftPerm_one (w : FinitaryPerm ℕ+) : shiftPerm w 1 = 1 :=
  Equiv.Perm.ofSubtype_apply_of_not_mem _ (by change ¬(1 : ℕ+) < 1; exact lt_irrefl _)

private theorem shiftPerm_successor (w : FinitaryPerm ℕ+) (i : ℕ+) :
    shiftPerm w (i + 1) = w i + 1 := by
  change Equiv.Perm.ofSubtype (shiftTailEquiv.permCongr w.val) (shiftTailEquiv i).val =
    (shiftTailEquiv (w i)).val
  rw [Equiv.Perm.ofSubtype_apply_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply]

private theorem exists_predecessor {j : ℕ+} (hj : 1 < j) : ∃ i : ℕ+, i + 1 = j := by
  let i := shiftTailEquiv.symm ⟨j, hj⟩
  refine ⟨i, ?_⟩
  have he := shiftTailEquiv.apply_symm_apply ⟨j, hj⟩
  exact congrArg Subtype.val he

private theorem shiftPerm_finite (w : FinitaryPerm ℕ+) : {j | shiftPerm w j ≠ j}.Finite := by
  apply (w.finite_movedSet.image (fun i : ℕ+ => i + 1)).subset
  intro j hj
  have hj1 : 1 < j := by
    have hp := j.pos
    have hn : j ≠ 1 := by
      intro he
      subst j
      exact hj (shiftPerm_one w)
    have hnn : (j : ℕ) ≠ 1 := fun he => hn (PNat.eq he)
    change 1 < (j : ℕ)
    omega
  obtain ⟨i, hi⟩ := exists_predecessor hj1
  refine ⟨i, ?_, hi⟩
  intro hfixed
  apply hj
  rw [←hi, shiftPerm_successor, hfixed]

/-- Insert one initial fixed position and translate the remaining positions and values by one. -/
def shiftRight (w : FinitaryPerm ℕ+) : FinitaryPerm ℕ+ :=
  ofPerm (shiftPerm w) (shiftPerm_finite w)

/-- A right-shifted permutation fixes its newly inserted first position. -/
@[simp] theorem shiftRight_apply_one (w : FinitaryPerm ℕ+) : shiftRight w 1 = 1 :=
  shiftPerm_one w

/-- Right shift translates every original position and its value by one. -/
theorem shiftRight_apply_add_one (w : FinitaryPerm ℕ+) (i : ℕ+) :
    shiftRight w (i + 1) = w i + 1 := shiftPerm_successor w i

/-- Right shift preserves the identity permutation. -/
@[simp] theorem shiftRight_one : shiftRight (1 : FinitaryPerm ℕ+) = 1 := by
  apply ext
  intro j
  by_cases hj : j = 1
  · subst j
    rw [shiftRight_apply_one, one_apply]
  · have hj1 : 1 < j := by
      have hp := j.pos
      have hn : (j : ℕ) ≠ 1 := fun he => hj (PNat.eq he)
      change 1 < (j : ℕ)
      omega
    obtain ⟨i, hi⟩ := exists_predecessor hj1
    rw [←hi, shiftRight_apply_add_one, one_apply, one_apply]

/-- Right shift preserves composition of permutations. -/
theorem shiftRight_mul (u v : FinitaryPerm ℕ+) :
    shiftRight (u * v) = shiftRight u * shiftRight v := by
  apply ext
  intro j
  by_cases hj : j = 1
  · subst j
    rw [mul_apply, shiftRight_apply_one, shiftRight_apply_one, shiftRight_apply_one]
  · have hj1 : 1 < j := by
      have hp := j.pos
      have hn : (j : ℕ) ≠ 1 := fun he => hj (PNat.eq he)
      change 1 < (j : ℕ)
      omega
    obtain ⟨i, hi⟩ := exists_predecessor hj1
    rw [←hi, shiftRight_apply_add_one, mul_apply (shiftRight u) (shiftRight v),
      shiftRight_apply_add_one,
      shiftRight_apply_add_one, mul_apply]

/-- Right shift is injective on finitary permutations. -/
theorem shiftRight_injective : Function.Injective shiftRight := by
  intro u v huv
  apply ext
  intro i
  have he := congrArg (fun w : FinitaryPerm ℕ+ => w (i + 1)) huv
  rw [shiftRight_apply_add_one, shiftRight_apply_add_one] at he
  apply PNat.eq
  have hn := congrArg (fun j : ℕ+ => (j : ℕ)) he
  change (u i : ℕ) + 1 = (v i : ℕ) + 1 at hn
  omega

/-- Right shift satisfies the signed-shift relation with amount one. -/
theorem shiftRight_signed (w : FinitaryPerm ℕ+) : SignedShift 1 w (shiftRight w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hp := i.pos
    omega
  · intro j hj
    have hp := j.pos
    have he : j = 1 := by
      apply PNat.eq
      change (j : ℕ) = 1
      omega
    subst j
    exact shiftRight_apply_one w
  · intro i j hij
    have he : j = i + 1 := by
      apply PNat.eq
      change (j : ℕ) = (i : ℕ) + 1
      omega
    subst j
    rw [shiftRight_apply_add_one]
    change (((w i : ℕ) + 1 : ℕ) : ℤ) = ((w i : ℕ) : ℤ) + 1
    omega

end FinitaryPerm
