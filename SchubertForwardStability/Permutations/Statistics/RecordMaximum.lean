import SchubertForwardStability.Permutations.Statistics.Records
import Mathlib.Tactic

/-! # The maximum value and the final bounded record

For a permutation supported in `[1, n]`, the position carrying the value `n` is a record,
and no later position up to `n` is a record. Hence the last record in `[1, n]` carries the
value `n`.
-/

namespace FinitaryPerm

/-- A position carrying the largest ambient value is a record. -/
theorem isRecord_of_value_max (n : ℕ) (w : FinitaryPerm ℕ+)
    (hw : IsSupported n w) (r : ℕ+) (hm : (w r : ℕ) = n) : IsRecord w r := by
  have hr : (r : ℕ) ≤ n := (hw.apply_le_iff r).mp (by omega)
  intro j hj
  have hjN : (j : ℕ) ≤ n := by
    change (j : ℕ) < (r : ℕ) at hj
    omega
  have hBound := (hw.apply_le_iff j).mpr hjN
  have hNe : w j ≠ w r := fun he => (ne_of_lt hj) (w.injective he)
  apply lt_of_le_of_ne
  · change (w j : ℕ) ≤ (w r : ℕ)
    omega
  · exact hNe

/-- An ambient position after the largest value cannot be a record. -/
theorem notRecord_after_value_max (n : ℕ) (w : FinitaryPerm ℕ+)
    (hw : IsSupported n w) (r j : ℕ+) (hm : (w r : ℕ) = n)
    (hrj : r < j) (hj : (j : ℕ) ≤ n) : ¬IsRecord w j := by
  intro hRecord
  have h := hRecord r hrj
  have hBound := (hw.apply_le_iff j).mpr hj
  change (w r : ℕ) < (w j : ℕ) at h
  omega

/-- The final record in a nonempty bounded interval carries its largest value. -/
theorem lastRecord_value (n : ℕ) (w : FinitaryPerm ℕ+) (hw : IsSupported n w)
    (r : ℕ+) (hr : r ∈ recordSet n w)
    (hLast : ∀ j ∈ recordSet n w, j ≤ r) : (w r : ℕ) = n := by
  have hrN := ((mem_recordSet n w r).mp hr).1
  have hRecord := ((mem_recordSet n w r).mp hr).2
  have hn : 0 < n := lt_of_lt_of_le r.pos hrN
  let N : ℕ+ := ⟨n, hn⟩
  let q := w⁻¹ N
  have hqN : (q : ℕ) ≤ n := (hw.inv.apply_le_iff N).mpr le_rfl
  have hqValue : (w q : ℕ) = n := by
    change (w (w⁻¹ N) : ℕ) = n
    rw [apply_inv_apply]
    rfl
  have hqRecord := isRecord_of_value_max n w hw q hqValue
  have hqr := hLast q ((mem_recordSet n w q).mpr ⟨hqN, hqRecord⟩)
  have hEqual : q = r := by
    by_contra hNe
    have hlt : q < r := lt_of_le_of_ne hqr hNe
    have h := hRecord q hlt
    have hBound := (hw.apply_le_iff r).mpr hrN
    change (w q : ℕ) < (w r : ℕ) at h
    omega
  rwa [hEqual] at hqValue

end FinitaryPerm
