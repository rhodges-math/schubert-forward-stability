import SchubertForwardStability.Permutations.Statistics.Blocks.TwoBlocks
import SchubertForwardStability.Permutations.Classes.GrassEncoding
import SchubertForwardStability.Permutations.Statistics.SuffixChoice

/-! # Maxima and support of ordered subset blocks

## Main results

The first block ends at the selected maximum. The second block increases throughout
the positive tail. Positions beyond the selected maximum are fixed, and a nonidentity
subset permutation has that maximum as its support bound.
-/

namespace FinitaryPerm

open scoped Classical

private theorem identity_of_card_zero (n : ℕ) (V : Finset ℕ+)
    (hV : V ⊆ positions n) (hz : V.card = 0) : grassmannianOfSubset n V hV = 1 := by
  apply grassmannianOfSubset_eq_one n V hV
  rw [Finset.card_eq_zero.mp hz, Finset.card_empty, positions_zero]

private theorem card_le_maximum (V : Finset ℕ+) : V.card ≤ V.sup PNat.val := by
  have hsub : V ⊆ positions (V.sup PNat.val) := by
    intro j hj
    exact (mem_positions _ _).mpr (Finset.le_sup (f := PNat.val) hj)
  simpa only [card_positions] using Finset.card_le_card hsub

/-- The selected block is strictly increasing on its positive positions. -/
theorem grassmannian_first_strictOn (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) :
    StrictMonoOn (grassmannianOfSubset n V hV) {i : ℕ+ | (i : ℕ) ≤ V.card} := by
  intro i hi j hj hij
  change (i : ℕ) ≤ V.card at hi
  change (j : ℕ) ≤ V.card at hj
  have hip : 0 < (i : ℕ) := i.2
  have hjp : 0 < (j : ℕ) := j.2
  have h := grassmannianOfSubset_first_mono n V hV
    (a := ⟨(i : ℕ) - 1, by omega⟩) (b := ⟨(j : ℕ) - 1, by omega⟩) (by
      change (i : ℕ) - 1 < (j : ℕ) - 1
      have hij' : (i : ℕ) < (j : ℕ) := hij
      omega)
  convert h using 1 <;> congr 1 <;> apply PNat.eq <;> dsimp <;> omega

/-- The complement block and all later fixed positions form an increasing tail. -/
theorem grassmannian_tail_strictOn (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) :
    StrictMonoOn (grassmannianOfSubset n V hV) {i : ℕ+ | V.card < (i : ℕ)} := by
  by_cases hz : V.card = 0
  · rw [identity_of_card_zero n V hV hz]
    intro i _ j _ hij
    exact hij
  · let k : ℕ+ := ⟨V.card, Nat.pos_of_ne_zero hz⟩
    apply strictMono_after_last_descent (r := k)
    intro j hj hd
    have he := grassmannianOfSubset_descent_eq n V hV j hd
    have hj' : V.card < (j : ℕ) := hj
    omega

/-- The final selected position carries the maximum selected value. -/
theorem grassmannian_first_maximum (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n)
    (hv : 0 < V.card) :
    (grassmannianOfSubset n V hV ⟨V.card, hv⟩ : ℕ) = V.sup PNat.val := by
  let k : ℕ+ := ⟨V.card, hv⟩
  have hk : k ∈ positions V.card := (mem_positions _ _).mpr le_rfl
  have him := grassmannianOfSubset_first_image n V hV
  apply le_antisymm
  · have hm : grassmannianOfSubset n V hV k ∈ V :=
      Eq.mp (congrArg (fun S : Finset ℕ+ => grassmannianOfSubset n V hV k ∈ S) him)
        (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
    exact Finset.le_sup (f := PNat.val) hm
  · apply Finset.sup_le
    intro j hj
    rw [←him] at hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hik : (i : ℕ) ≤ V.card := (mem_positions _ _).mp hi
    exact (grassmannian_first_strictOn n V hV).monotoneOn hik
      (show (k : ℕ) ≤ V.card from le_rfl) hik

/-- A nonempty selected maximum bounds the positive support statistic. -/
theorem grassmannian_forward_le_max (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n)
    (hv : 0 < V.card) :
    (grassmannianOfSubset n V hV).forwardStability ≤ V.sup PNat.val := by
  have hM : 0 < V.sup PNat.val := hv.trans_le (card_le_maximum V)
  exact twoBlock_forward_le (k := ⟨V.card, hv⟩) (M := ⟨V.sup PNat.val, hM⟩)
    (grassmannian_first_strictOn n V hV) (grassmannian_tail_strictOn n V hV)
    (PNat.eq (grassmannian_first_maximum n V hV hv))

/-- Every position above the selected maximum is fixed, including empty selections. -/
theorem grassmannian_fixed_above_max (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n)
    (j : ℕ+) (hj : V.sup PNat.val < (j : ℕ)) : grassmannianOfSubset n V hV j = j := by
  by_cases hz : V.card = 0
  · rw [identity_of_card_zero n V hV hz, one_apply]
  · have hf := grassmannian_forward_le_max n V hV (Nat.pos_of_ne_zero hz)
    exact (grassmannianOfSubset n V hV).isSupported_forwardStability j (hf.trans_lt hj)

/-- A nonidentity ordered-subset permutation has the selected maximum as support bound. -/
theorem grassmannian_forward_eq_max (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n)
    (hw : grassmannianOfSubset n V hV ≠ 1) :
    (grassmannianOfSubset n V hV).forwardStability = V.sup PNat.val := by
  have hv : 0 < V.card := by
    by_contra hn
    exact hw (identity_of_card_zero n V hV (by omega))
  have hM : 0 < V.sup PNat.val := hv.trans_le (card_le_maximum V)
  obtain ⟨j, hd⟩ := exists_descent_of_ne_one (grassmannianOfSubset n V hV) hw
  have he := grassmannianOfSubset_descent_eq n V hV j hd
  have hj := (grassmannianOfSubset n V hV).isSupported_forwardStability.descent_lt hd
  have hf := grassmannian_forward_le_max n V hV hv
  have hkM : V.card < V.sup PNat.val := by omega
  exact twoBlock_forward_eq (k := ⟨V.card, hv⟩) (M := ⟨V.sup PNat.val, hM⟩)
    (grassmannian_first_strictOn n V hV) (grassmannian_tail_strictOn n V hV)
    (PNat.eq (grassmannian_first_maximum n V hV hv)) hkM

/-- Non-record positions of any subset encoding form the interval after its sampled block. -/
theorem grassmannian_notRecord_iff (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) (j : ℕ+) :
    ¬IsRecord (grassmannianOfSubset n V hV) j ↔ V.card < (j : ℕ) ∧ (j : ℕ) ≤ V.sup PNat.val := by
  by_cases hz : V.card = 0
  · have hM : V.sup PNat.val = 0 := by simp [Finset.card_eq_zero.mp hz]
    rw [identity_of_card_zero n V hV hz, hz, hM]
    have hj : 0 < (j : ℕ) := j.2
    simp only [isRecord_one, not_true_eq_false, not_le.mpr hj, and_false]
  · have hv : 0 < V.card := Nat.pos_of_ne_zero hz
    have hM : 0 < V.sup PNat.val := hv.trans_le (card_le_maximum V)
    rw [not_isRecord_iff_earlier_larger]
    exact twoBlock_nonRecord_interval_iff (k := ⟨V.card, hv⟩)
      (M := ⟨V.sup PNat.val, hM⟩) (grassmannian_first_strictOn n V hV)
      (grassmannian_tail_strictOn n V hV) (grassmannianOfSubset n V hV).injective
      (card_le_maximum V) (PNat.eq (grassmannian_first_maximum n V hV hv))
      (fun j hj => grassmannian_fixed_above_max n V hV j hj)

/-- The intrinsic non-record tail of a subset encoding has the three sampled-block pieces. -/
theorem grassmannian_tail_formula (n : ℕ) (V : Finset ℕ+) (hV : V ⊆ positions n) (i : ℕ+) :
    (grassmannianOfSubset n V hV).nonRecordsFrom i =
      if (i : ℕ) ≤ V.card then V.sup PNat.val - V.card
      else if (i : ℕ) ≤ V.sup PNat.val then V.sup PNat.val - (i : ℕ) + 1 else 0 := by
  by_cases hz : V.card = 0
  · have hM : V.sup PNat.val = 0 := by simp [Finset.card_eq_zero.mp hz]
    rw [identity_of_card_zero n V hV hz, nonRecordsFrom_one, hz, hM]
    have hi : 0 < (i : ℕ) := i.2
    simp only [not_le.mpr hi, ite_false]
  · have hv : 0 < V.card := Nat.pos_of_ne_zero hz
    have hM : 0 < V.sup PNat.val := hv.trans_le (card_le_maximum V)
    exact twoBlock_tail_of_max (k := ⟨V.card, hv⟩) (M := ⟨V.sup PNat.val, hM⟩)
      (grassmannian_first_strictOn n V hV) (grassmannian_tail_strictOn n V hV)
      (card_le_maximum V) (PNat.eq (grassmannian_first_maximum n V hV hv)) i

end FinitaryPerm
