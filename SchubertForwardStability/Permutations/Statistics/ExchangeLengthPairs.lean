import SchubertForwardStability.Permutations.Statistics.Inversions
import SchubertForwardStability.Permutations.Statistics.SuffixAscent

/-! # Transport of inversion pairs under an exchange

## Main definitions

* `exchangePair`: exchange both indices outside the closed endpoint interval, fixing inner pairs.

## Main results

The pair transport is an involution preserving position order. For an ascent, it
injects original inversions into exchanged inversions, omitting the endpoint pair.
For a gap-free ascent, these are exactly the inversions other than the endpoint pair.

## Implementation notes

Pairs wholly inside the endpoint interval are fixed. All other pairs use the same
transposition as the permutation, so their value comparisons remain unchanged.
-/

namespace FinitaryPerm

open scoped Classical

/-- Exchange both indices of an outer pair and leave a pair inside the endpoint interval fixed. -/
def exchangePair (q r : ℕ+) (p : ℕ+ × ℕ+) : ℕ+ × ℕ+ :=
  if p.1 < q ∨ r < p.2 then (swap q r p.1, swap q r p.2) else p

private theorem swap_twice (q r k : ℕ+) : swap q r (swap q r k) = k := by
  simpa only [swap_inv] using inv_apply_apply (swap q r) k

/-- Transport fixes pairs whose two indices lie inside the endpoint interval. -/
theorem exchangePair_inner {q r a b : ℕ+} (ha : q ≤ a) (hb : b ≤ r) :
    exchangePair q r (a, b) = (a, b) := by
  have hn : ¬(a < q ∨ r < b) := fun h => h.elim (not_lt_of_ge ha) (not_lt_of_ge hb)
  exact ite_eq_right hn

private theorem outer_stable {q r a b : ℕ+} (hqr : q < r) (ho : a < q ∨ r < b) :
    swap q r a < q ∨ r < swap q r b := by
  rcases ho with ha | hb
  · left
    simpa only [swap_apply_of_ne (ne_of_lt ha) (ne_of_lt (ha.trans hqr))] using ha
  · right
    simpa only [swap_apply_of_ne (ne_of_gt (hqr.trans hb)) (ne_of_gt hb)] using hb

/-- Pair transport is an involution for ordered endpoints. -/
theorem exchangePair_involutive {q r : ℕ+} (hqr : q < r) :
    Function.Involutive (exchangePair q r) := by
  rintro ⟨a, b⟩
  by_cases ho : a < q ∨ r < b
  · have ho' := outer_stable hqr ho
    simp only [exchangePair, ite_eq_left ho, ite_eq_left ho', swap_twice]
  · simp only [exchangePair, ite_eq_right ho]

/-- Ordered-endpoint pair transport is injective. -/
theorem exchangePair_injective {q r : ℕ+} (hqr : q < r) :
    Function.Injective (exchangePair q r) := (exchangePair_involutive hqr).injective

private theorem swapped_order {q r a b : ℕ+} (hqr : q < r) (hab : a < b)
    (ho : a < q ∨ r < b) : swap q r a < swap q r b := by
  rcases ho with ha | hb
  · rw [swap_apply_of_ne (ne_of_lt ha) (ne_of_lt (ha.trans hqr))]
    by_cases hbq : b = q
    · subst b
      simpa only [swap_apply_left] using ha.trans hqr
    · by_cases hbr : b = r
      · subst b
        simpa only [swap_apply_right] using ha
      · simpa only [swap_apply_of_ne hbq hbr] using hab
  · rw [swap_apply_of_ne (ne_of_gt (hqr.trans hb)) (ne_of_gt hb)]
    by_cases haq : a = q
    · subst a
      simpa only [swap_apply_left] using hb
    · by_cases har : a = r
      · subst a
        simpa only [swap_apply_right] using hqr.trans hb
      · simpa only [swap_apply_of_ne haq har] using hab

private theorem exchangePair_order_imp {q r : ℕ+} (hqr : q < r) {p : ℕ+ × ℕ+}
    (hp : p.1 < p.2) : (exchangePair q r p).1 < (exchangePair q r p).2 := by
  rcases p with ⟨a, b⟩
  by_cases ho : a < q ∨ r < b
  · simpa only [exchangePair, ite_eq_left ho] using swapped_order hqr hp ho
  · simpa only [exchangePair, ite_eq_right ho] using hp

/-- Pair transport preserves strict position order. -/
theorem exchangePair_order {q r : ℕ+} (hqr : q < r) (p : ℕ+ × ℕ+) :
    (exchangePair q r p).1 < (exchangePair q r p).2 ↔ p.1 < p.2 := by
  constructor
  · intro hp
    simpa only [exchangePair_involutive hqr p] using exchangePair_order_imp hqr hp
  · exact exchangePair_order_imp hqr

private theorem inversion_outer {w : FinitaryPerm ℕ+} {q r a b : ℕ+}
    (hqr : q < r) (ho : a < q ∨ r < b) :
    exchangePair q r (a, b) ∈ (w * swap q r).inversionSet ↔ (a, b) ∈ w.inversionSet := by
  have hord := exchangePair_order hqr (a, b)
  simp only [exchangePair, ite_eq_left ho] at hord ⊢
  simp only [mem_inversionSet, mul_apply, swap_twice, hord]

private theorem inversion_inner_imp {w : FinitaryPerm ℕ+} {q r a b : ℕ+}
    (hv : w q < w r) (ha : q ≤ a) (hb : b ≤ r)
    (hab : a < b) (hinv : w b < w a) : (w * swap q r) b < (w * swap q r) a := by
  by_cases haq : a = q
  · subst a
    by_cases hbr : b = r
    · subst b
      exact False.elim ((not_lt_of_gt hv) hinv)
    · rw [mul_apply, swap_apply_of_ne (ne_of_gt hab) hbr, mul_apply, swap_apply_left]
      exact hinv.trans hv
  · by_cases hbr : b = r
    · subst b
      rw [mul_apply, swap_apply_right, mul_apply, swap_apply_of_ne haq (ne_of_lt hab)]
      exact hv.trans hinv
    · have hbn : b ≠ q := ne_of_gt (lt_of_le_of_lt ha hab)
      have han : a ≠ r := ne_of_lt (lt_of_lt_of_le hab hb)
      simpa only [mul_apply, swap_apply_of_ne hbn hbr, swap_apply_of_ne haq han] using hinv

/-- An ascent transports each inversion to a distinct inversion other than the endpoint pair. -/
theorem exchangePair_mem_ascent {w : FinitaryPerm ℕ+} {q r : ℕ+} (hqr : q < r)
    (hv : w q < w r) {p : ℕ+ × ℕ+} (hp : p ∈ w.inversionSet) :
    exchangePair q r p ∈ (w * swap q r).inversionSet ∧ exchangePair q r p ≠ (q, r) := by
  rcases p with ⟨a, b⟩
  obtain ⟨hab, hinv⟩ := (mem_inversionSet w a b).mp hp
  have hmem : exchangePair q r (a, b) ∈ (w * swap q r).inversionSet := by
    by_cases ho : a < q ∨ r < b
    · exact (inversion_outer hqr ho).mpr hp
    · have ha : q ≤ a := le_of_not_gt (fun h => ho (Or.inl h))
      have hb : b ≤ r := le_of_not_gt (fun h => ho (Or.inr h))
      rw [exchangePair_inner ha hb, mem_inversionSet]
      exact ⟨hab, inversion_inner_imp hv ha hb hab hinv⟩
  refine ⟨hmem, ?_⟩
  intro he
  have hfix : exchangePair q r (q, r) = (q, r) := exchangePair_inner le_rfl le_rfl
  have hpqr : (a, b) = (q, r) := exchangePair_injective hqr (he.trans hfix.symm)
  have hbad : a = q := congrArg Prod.fst hpqr
  have hbad' : b = r := congrArg Prod.snd hpqr
  rw [hbad, hbad'] at hinv
  exact (not_lt_of_gt hv) hinv

private theorem inversion_inner_rev {w : FinitaryPerm ℕ+} {q r a b : ℕ+}
    (h : GapFreeAscent w q r) (ha : q ≤ a) (hb : b ≤ r) (hab : a < b)
    (hne : (a, b) ≠ (q, r)) (hinv : (w * swap q r) b < (w * swap q r) a) :
    w b < w a := by
  by_cases haq : a = q
  · subst a
    by_cases hbr : b = r
    · subst b
      exact False.elim (hne rfl)
    · rw [mul_apply, swap_apply_of_ne (ne_of_gt hab) hbr,
        mul_apply, swap_apply_left] at hinv
      have hbr' : b < r := lt_of_le_of_ne hb hbr
      have hn : ¬w q < w b := fun hv => h.gap b hab hbr' ⟨hv, hinv⟩
      have hval : w b ≠ w q := fun he => (ne_of_gt hab) (w.injective he)
      exact lt_of_le_of_ne (le_of_not_gt hn) hval
  · by_cases hbr : b = r
    · subst b
      rw [mul_apply, swap_apply_right,
        mul_apply, swap_apply_of_ne haq (ne_of_lt hab)] at hinv
      have hqa : q < a := lt_of_le_of_ne ha (Ne.symm haq)
      have hn : ¬w a < w r := fun hv => h.gap a hqa hab ⟨hinv, hv⟩
      have hval : w r ≠ w a := fun he => (ne_of_gt hab) (w.injective he)
      exact lt_of_le_of_ne (le_of_not_gt hn) hval
    · have hbn : b ≠ q := ne_of_gt (lt_of_le_of_lt ha hab)
      have han : a ≠ r := ne_of_lt (lt_of_lt_of_le hab hb)
      simpa only [mul_apply, swap_apply_of_ne hbn hbr, swap_apply_of_ne haq han] using hinv

/-- A gap-free ascent transports precisely the inversions other than the endpoint pair. -/
theorem GapFreeAscent.exchangePair_mem_iff {w : FinitaryPerm ℕ+} {q r : ℕ+}
    (h : GapFreeAscent w q r) (p : ℕ+ × ℕ+) :
    (exchangePair q r p ∈ (w * swap q r).inversionSet ∧ exchangePair q r p ≠ (q, r)) ↔
      p ∈ w.inversionSet := by
  rcases p with ⟨a, b⟩
  constructor
  · rintro ⟨hinv, hne⟩
    by_cases ho : a < q ∨ r < b
    · exact (inversion_outer h.left_lt ho).mp hinv
    · have ha : q ≤ a := le_of_not_gt (fun hj => ho (Or.inl hj))
      have hb : b ≤ r := le_of_not_gt (fun hj => ho (Or.inr hj))
      rw [exchangePair_inner ha hb] at hinv hne
      obtain ⟨hab, hv⟩ := (mem_inversionSet _ a b).mp hinv
      exact (mem_inversionSet w a b).mpr ⟨hab, inversion_inner_rev h ha hb hab hne hv⟩
  · exact exchangePair_mem_ascent h.left_lt h.value_lt

end FinitaryPerm
