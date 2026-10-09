import SchubertForwardStability.Permutations.Statistics.ExchangeLengthPairs

/-! # Length covers for right transpositions

## Main definitions

* `exchangeInvImage`: the finite image of the original inversion set under pair transport.

## Main results

A right transposition at ordered positions increases inversion length by one exactly
when the endpoint values form a gap-free ascent. An ascent with an intervening value
strictly between its endpoint values increases length by at least three.

## Implementation notes

Pair transport gives a cardinality-preserving image. One or three explicit exchanged
inversions are absent from that image, depending on the intervening values.
-/

namespace FinitaryPerm

open scoped Classical

/-- The image of the original inversions under the endpoint pair transport. -/
noncomputable def exchangeInvImage (w : FinitaryPerm ℕ+) (q r : ℕ+) : Finset (ℕ+ × ℕ+) :=
  w.inversionSet.image (exchangePair q r)

/-- Membership in the transported image is tested by applying the same involution. -/
theorem mem_exchangeInvImage {w : FinitaryPerm ℕ+} {q r : ℕ+} (hqr : q < r)
    (p : ℕ+ × ℕ+) : p ∈ exchangeInvImage w q r ↔ exchangePair q r p ∈ w.inversionSet := by
  rw [exchangeInvImage, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, he⟩
    have hback : exchangePair q r p = x := by
      rw [←he, exchangePair_involutive hqr x]
    simpa only [hback] using hx
  · intro hp
    exact ⟨exchangePair q r p, hp, exchangePair_involutive hqr p⟩

/-- Pair transport preserves the cardinality of the inversion set. -/
theorem card_exchangeInvImage {w : FinitaryPerm ℕ+} {q r : ℕ+} (hqr : q < r) :
    (exchangeInvImage w q r).card = w.length := by
  rw [exchangeInvImage, Finset.card_image_of_injective _ (exchangePair_injective hqr)]
  rfl

/-- For an ascent, the transported image omits the new endpoint inversion. -/
theorem exchangeInvImage_subset {w : FinitaryPerm ℕ+} {q r : ℕ+} (hqr : q < r)
    (hv : w q < w r) :
    exchangeInvImage w q r ⊆ (w * swap q r).inversionSet.erase (q, r) := by
  intro p hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hmem, hne⟩ := exchangePair_mem_ascent hqr hv hx
  exact Finset.mem_erase.mpr ⟨hne, hmem⟩

/-- An inner pair absent from the original inversions is absent from the transported image. -/
theorem not_mem_exchangeInvImage_inner {w : FinitaryPerm ℕ+} {q r a b : ℕ+}
    (hqr : q < r) (ha : q ≤ a) (hb : b ≤ r) (hp : (a, b) ∉ w.inversionSet) :
    (a, b) ∉ exchangeInvImage w q r := by
  rw [mem_exchangeInvImage hqr, exchangePair_inner ha hb]
  exact hp

private theorem endpoint_inversion {w : FinitaryPerm ℕ+} {q r : ℕ+}
    (hqr : q < r) (hv : w q < w r) : (q, r) ∈ (w * swap q r).inversionSet := by
  rw [mem_inversionSet, mul_apply, swap_apply_right, mul_apply, swap_apply_left]
  exact ⟨hqr, hv⟩

/-- Exchanging any ascent raises inversion length by at least one. -/
theorem length_exchange_ge {w : FinitaryPerm ℕ+} {q r : ℕ+}
    (hqr : q < r) (hv : w q < w r) : w.length + 1 ≤ (w * swap q r).length := by
  have hcard := Finset.card_le_card (exchangeInvImage_subset hqr hv)
  rw [card_exchangeInvImage hqr] at hcard
  have hrestore := Finset.card_erase_add_one (endpoint_inversion hqr hv)
  change _ + 1 = (w * swap q r).length at hrestore
  omega

/-- A gap-free ascent's transported image is the exchanged inversion set
without its endpoint pair. -/
theorem GapFreeAscent.exchangeInvImage_eq {w : FinitaryPerm ℕ+} {q r : ℕ+}
    (h : GapFreeAscent w q r) :
    exchangeInvImage w q r = (w * swap q r).inversionSet.erase (q, r) := by
  apply Finset.Subset.antisymm (exchangeInvImage_subset h.left_lt h.value_lt)
  intro p hp
  obtain ⟨hne, hinv⟩ := Finset.mem_erase.mp hp
  rw [mem_exchangeInvImage h.left_lt]
  have hiff := h.exchangePair_mem_iff (exchangePair q r p)
  rw [exchangePair_involutive h.left_lt p] at hiff
  exact hiff.mp ⟨hinv, hne⟩

/-- Exchanging a gap-free ascent raises inversion length by exactly one. -/
theorem GapFreeAscent.length_exchange {w : FinitaryPerm ℕ+} {q r : ℕ+}
    (h : GapFreeAscent w q r) : (w * swap q r).length = w.length + 1 := by
  have hcard := congrArg Finset.card h.exchangeInvImage_eq
  rw [card_exchangeInvImage h.left_lt] at hcard
  have hrestore := Finset.card_erase_add_one (endpoint_inversion h.left_lt h.value_lt)
  change _ + 1 = (w * swap q r).length at hrestore
  omega

/-- An intervening value between ascent endpoints forces at least three new inversions. -/
theorem length_exchange_ge_three {w : FinitaryPerm ℕ+} {q r k : ℕ+}
    (hqr : q < r) (hqk : q < k) (hkr : k < r) (hqv : w q < w k) (hvr : w k < w r) :
    w.length + 3 ≤ (w * swap q r).length := by
  let t : Finset (ℕ+ × ℕ+) := {(q, r), (q, k), (k, r)}
  have hqrinv := endpoint_inversion hqr (hqv.trans hvr)
  have hqkinv : (q, k) ∈ (w * swap q r).inversionSet := by
    rw [mem_inversionSet, mul_apply, swap_apply_of_ne (ne_of_gt hqk) (ne_of_lt hkr),
      mul_apply, swap_apply_left]
    exact ⟨hqk, hvr⟩
  have hkrinv : (k, r) ∈ (w * swap q r).inversionSet := by
    rw [mem_inversionSet, mul_apply, swap_apply_right,
      mul_apply, swap_apply_of_ne (ne_of_gt hqk) (ne_of_lt hkr)]
    exact ⟨hkr, hqv⟩
  have hnqr : (q, r) ∉ exchangeInvImage w q r := by
    apply not_mem_exchangeInvImage_inner hqr le_rfl le_rfl
    intro hp
    exact (not_lt_of_gt (hqv.trans hvr)) ((mem_inversionSet w q r).mp hp).2
  have hnqk : (q, k) ∉ exchangeInvImage w q r := by
    apply not_mem_exchangeInvImage_inner hqr le_rfl (le_of_lt hkr)
    intro hp
    exact (not_lt_of_gt hqv) ((mem_inversionSet w q k).mp hp).2
  have hnkr : (k, r) ∉ exchangeInvImage w q r := by
    apply not_mem_exchangeInvImage_inner hqr (le_of_lt hqk) le_rfl
    intro hp
    exact (not_lt_of_gt hvr) ((mem_inversionSet w k r).mp hp).2
  have ht : t ⊆ (w * swap q r).inversionSet := by
    intro p hp
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption
  have hd : Disjoint (exchangeInvImage w q r) t := by
    apply Finset.disjoint_left.mpr
    intro p hp hpt
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at hpt
    rcases hpt with rfl | rfl | rfl
    · exact hnqr hp
    · exact hnqk hp
    · exact hnkr hp
  have hne1 : (q, r) ≠ (q, k) := fun he => (ne_of_gt hkr) (congrArg Prod.snd he)
  have hne2 : (q, r) ≠ (k, r) := fun he => (ne_of_lt hqk) (congrArg Prod.fst he)
  have hne3 : (q, k) ≠ (k, r) := fun he => (ne_of_lt hqk) (congrArg Prod.fst he)
  have htcard : t.card = 3 := by simp [t, hne1, hne2, hne3]
  have hi : exchangeInvImage w q r ⊆ (w * swap q r).inversionSet :=
    (exchangeInvImage_subset hqr (hqv.trans hvr)).trans (Finset.erase_subset _ _)
  have hc := Finset.card_le_card (Finset.union_subset hi ht)
  rw [Finset.card_union_of_disjoint hd, card_exchangeInvImage hqr, htcard] at hc
  exact hc

/-- A right transposition is an upward length cover exactly at a gap-free ascent. -/
theorem length_exchange_cover_iff {w : FinitaryPerm ℕ+} {q r : ℕ+} (hqr : q < r) :
    (w * swap q r).length = w.length + 1 ↔ GapFreeAscent w q r := by
  constructor
  · intro hlength
    have hv : w q < w r := by
      rcases lt_trichotomy (w q) (w r) with hv | he | hv
      · exact hv
      · exact False.elim ((ne_of_lt hqr) (w.injective he))
      · have hswap : (swap q r : FinitaryPerm ℕ+) * swap q r = 1 := by
          simpa only [swap_inv] using mul_inv_cancel (swap q r)
        have hback : (w * swap q r) * swap q r = w := by
          rw [mul_assoc, hswap, mul_one]
        have hv' : (w * swap q r) q < (w * swap q r) r := by
          simpa only [mul_apply, swap_apply_left, swap_apply_right] using hv
        have hge := length_exchange_ge hqr hv'
        rw [hback] at hge
        omega
    refine ⟨hqr, hv, ?_⟩
    intro k hqk hkr hbetween
    have hge := length_exchange_ge_three hqr hqk hkr hbetween.1 hbetween.2
    omega
  · exact GapFreeAscent.length_exchange

end FinitaryPerm
