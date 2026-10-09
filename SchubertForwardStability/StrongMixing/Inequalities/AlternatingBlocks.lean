import SchubertForwardStability.StrongMixing.Inequalities.SeparatedProducts

/-!
# Explicit alternating interval blocks

Intersecting a finite coordinate set with consecutive equal-length intervals
partitions its sum. The even and odd interval families separately admit integer
past/future cuts with a gap at least the block length.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StrongMixing

/-- The part of `A` in the `q`th consecutive integer interval of length `len`,
starting from translation `a`. Zero length gives an empty block. -/
def intervalChunk (A : Finset ℤ) (a : ℤ) (len q : ℕ) : Finset ℤ :=
  A ∩ Finset.Ico (a + (q * len : ℕ)) (a + ((q + 1) * len : ℕ))

/-- An intersected interval chunk is contained in its interval of
length `len`, with no assumption on the surrounding finite coordinate set. -/
theorem intervalChunk_subset (A : Finset ℤ) (a : ℤ) (len q : ℕ) :
    intervalChunk A a len q ⊆ Finset.Ico (a + (q * len : ℕ))
      (a + (q * len : ℕ) + len) := by
  have hid : a + (((q + 1) * len : ℕ) : ℤ) = a + ((q * len : ℕ) : ℤ) + len := by
    push_cast
    ring
  rw [← hid]
  exact Finset.inter_subset_right

/-- The number of selected coordinates in a chunk is at most its integer
interval length, including zero-length and empty-set boundaries. -/
theorem intervalChunk_card_le (A : Finset ℤ) (a : ℤ) (len q : ℕ) :
    (intervalChunk A a len q).card ≤ len := by
  have h := Finset.card_le_card (intervalChunk_subset A a len q)
  simpa only [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast] using h

/-- The sum over `p` consecutive intersected chunks equals the sum over the
intersection of `A` with their full integer interval. No coverage hypothesis is
needed; coordinates outside that interval do not appear on either side. -/
theorem interval_chunks_sum (A : Finset ℤ) (a : ℤ) (len p : ℕ) (f : ℤ → ℝ) :
    (∑ q ∈ Finset.range p, ∑ j ∈ intervalChunk A a len q, f j) =
      ∑ j ∈ A ∩ Finset.Ico a (a + (p * len : ℕ)), f j := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ, ih]
    let b : ℤ := a + (p * len : ℕ)
    let c : ℤ := a + ((p + 1) * len : ℕ)
    have hab : a ≤ b := by
      exact le_add_of_nonneg_right (Nat.cast_nonneg (p * len))
    have hbc : b ≤ c := by
      have hmul : ((p * len : ℕ) : ℤ) ≤ (((p + 1) * len : ℕ) : ℤ) := by
        exact_mod_cast Nat.mul_le_mul_right len (Nat.le_succ p)
      exact add_le_add le_rfl hmul
    have hd : Disjoint (A ∩ Finset.Ico a b) (A ∩ Finset.Ico b c) :=
      (Finset.Ico_disjoint_Ico_consecutive a b c).mono
        Finset.inter_subset_right Finset.inter_subset_right
    change (∑ j ∈ A ∩ Finset.Ico a b, f j) +
      (∑ j ∈ A ∩ Finset.Ico b c, f j) = ∑ j ∈ A ∩ Finset.Ico a c, f j
    rw [← Finset.sum_union hd, ← Finset.inter_union_distrib_left,
      Finset.Ico_union_Ico_eq_Ico hab hbc]

/-- Either parity family of chunks has every nontrivial prefix separated from
the remaining finite suffix by a natural lag at least `len`. Empty blocks and zero
length are allowed. -/
theorem alternating_chunks_separated (A : Finset ℤ) (a : ℤ) (len parity p : ℕ) :
    ∀ k : ℕ, 1 ≤ k → k < p → ∃ cut : ℤ,
      (∀ i : ℕ, i < k → ∀ j ∈ intervalChunk A a len (2 * i + parity), j ≤ cut) ∧
      (∀ i : ℕ, k ≤ i → i < p →
        ∀ j ∈ intervalChunk A a len (2 * i + parity), cut + (len : ℤ) ≤ j) := by
  intro k hk _hkp
  let cut : ℤ := a + ((2 * k + parity - 1) * len : ℕ) - 1
  refine ⟨cut, ?_, ?_⟩
  · intro i hik j hj
    have hj := (Finset.mem_Ico.mp (Finset.mem_inter.mp hj).2).2
    have hi : (2 * i + parity + 1) * len ≤ (2 * k + parity - 1) * len :=
      Nat.mul_le_mul_right len (by omega)
    have hic : (((2 * i + parity + 1) * len : ℕ) : ℤ) ≤
        (((2 * k + parity - 1) * len : ℕ) : ℤ) := by exact_mod_cast hi
    dsimp [cut]
    omega
  · intro i hki _hip j hj
    have hj := (Finset.mem_Ico.mp (Finset.mem_inter.mp hj).2).1
    have hi : (2 * k + parity) * len ≤ (2 * i + parity) * len :=
      Nat.mul_le_mul_right len (by omega)
    have hic : (((2 * k + parity) * len : ℕ) : ℤ) ≤
        (((2 * i + parity) * len : ℕ) : ℤ) := by exact_mod_cast hi
    have hid : (2 * k + parity - 1) * len + len = (2 * k + parity) * len := by
      calc
        _ = (2 * k + parity - 1 + 1) * len := by ring
        _ = _ := by rw [Nat.sub_add_cancel (by omega)]
    have hidc : (((2 * k + parity - 1) * len : ℕ) : ℤ) + (len : ℤ) =
        (((2 * k + parity) * len : ℕ) : ℤ) := by exact_mod_cast hid
    dsimp [cut]
    omega

/-- A real sum over `2*p` natural indices splits into its even and odd indexed
sums over `p` indices, including the empty-range boundary. -/
theorem sum_range_even_odd (f : ℕ → ℝ) (p : ℕ) :
    (∑ q ∈ Finset.range (2 * p), f q) =
      (∑ i ∈ Finset.range p, f (2 * i)) + ∑ i ∈ Finset.range p, f (2 * i + 1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hid : 2 * (p + 1) = (2 * p + 1) + 1 := by omega
    rw [hid]
    simp only [Finset.sum_range_succ, ih]
    ring

/-- If `2*p` consecutive chunks cover `A`, its coordinate sum is exactly the
sum of the even chunk sums and the odd chunk sums. This decomposition is used
before the two separately separated families are combined probabilistically. -/
theorem alternating_chunks_sum (A : Finset ℤ) (a : ℤ) (len p : ℕ) (f : ℤ → ℝ)
    (hA : A ⊆ Finset.Ico a (a + (2 * p * len : ℕ))) :
    (∑ j ∈ A, f j) = (∑ i ∈ Finset.range p, ∑ j ∈ intervalChunk A a len (2 * i), f j) +
      ∑ i ∈ Finset.range p, ∑ j ∈ intervalChunk A a len (2 * i + 1), f j := by
  have h := interval_chunks_sum A a len (2 * p) f
  rw [Finset.inter_eq_left.mpr hA, sum_range_even_odd] at h
  exact h.symm

end StrongMixing
