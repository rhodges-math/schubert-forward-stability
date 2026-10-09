import SchubertForwardStability.SchubertPolynomials.Products.RecordBound
import SchubertForwardStability.Permutations.Statistics.RecordBound

/-! # Schubert product stability as a function of bounded record sets

The non-record support bound and all tail counts are read directly from the
complement of a bounded record set. Substitution into the global record maximum
expresses product forward stability using only the two finite record sets.
-/

namespace FinitaryPerm

open scoped Classical

/-- Within any support interval, the record-set complement is the full non-record support. -/
theorem nonRecordPositions_eq_sdiff {n : ℕ} {w : FinitaryPerm ℕ+} (hw : IsSupported n w) :
    w.nonRecordPositions = positions n \ recordSet n w := by
  ext j
  simp only [mem_nonRecordPositions, Finset.mem_sdiff, mem_positions, mem_recordSet]
  constructor
  · intro hn
    have hj : (j : ℕ) ≤ n := le_of_not_gt (fun h => hn (hw.isRecord_above h))
    exact ⟨hj, fun h => hn h.2⟩
  · rintro ⟨hj, hn⟩ hr
    exact hn ⟨hj, hr⟩

/-- The positive support bound extracted from the non-record positions of a finite record set. -/
noncomputable def recordSupportBound (n : ℕ) (R : Finset ℕ+) : ℕ :=
  max 1 ((positions n \ R).sup PNat.val)

/-- The record-set support bound equals the permutation's least positive support bound. -/
theorem recordSupportBound_eq {n : ℕ} {w : FinitaryPerm ℕ+} (hw : IsSupported n w) :
    recordSupportBound n (recordSet n w) = w.forwardStability := by
  rw [recordSupportBound, ← nonRecordPositions_eq_sdiff hw]
  exact nonRecordBound_eq w

/-- The global non-record tail count extracted from a finite record set. -/
noncomputable def recordTailCount (n : ℕ) (R : Finset ℕ+) (i : ℕ+) : ℕ :=
  ((positions n \ R).filter fun j => i ≤ j).card

/-- Extracted record-set tail counts equal the global non-record tail counts. -/
theorem recordTailCount_eq {n : ℕ} {w : FinitaryPerm ℕ+} (hw : IsSupported n w) (i : ℕ+) :
    recordTailCount n (recordSet n w) i = w.nonRecordsFrom i := by
  rw [recordTailCount, ← nonRecordPositions_eq_sdiff hw, nonRecordsFrom_eq_card]
  congr 1
  ext j
  simp only [Finset.mem_filter, mem_nonRecordPositions, mem_tailPositions]
  constructor
  · rintro ⟨hn, hi⟩
    exact ⟨⟨le_of_not_gt (fun h => hn (w.isRecord_above h)), hi⟩, hn⟩
  · rintro ⟨⟨_, hi⟩, hn⟩
    exact ⟨hn, hi⟩

/-- The paired global non-record maximum as a function of two bounded record sets. -/
noncomputable def recordPairBound (n : ℕ) (P : Finset ℕ+ × Finset ℕ+) : ℕ :=
  (positions (max (recordSupportBound n P.1) (recordSupportBound n P.2) + 1)).sup fun i =>
    recordTailCount n P.1 i + recordTailCount n P.2 i + (i : ℕ) - 1

end FinitaryPerm

namespace SchubertPolynomial

open FinitaryPerm

/-- Supported Schubert product forward stability factors through its two record sets. -/
theorem productForward_eq_recordPairBound {n : ℕ} {u v : FinitaryPerm ℕ+}
    (hu : IsSupported n u) (hv : IsSupported n v) :
    productForwardStability u v = recordPairBound n (recordSet n u, recordSet n v) := by
  rw [productForwardStability_eq_recordBound]
  simp only [recordPairBound, recordSupportBound_eq hu, recordSupportBound_eq hv,
    recordTailCount_eq hu, recordTailCount_eq hv]
  rfl

end SchubertPolynomial
