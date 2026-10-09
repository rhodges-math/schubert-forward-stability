import SchubertForwardStability.Permutations.Random.Records
import SchubertForwardStability.Permutations.ForMathlib.UniformEvents

/-! # Compatible finite record prefixes

`recordPrefix n w` is the permutation of `S_n` with the same first `n` left inversion
counts as `w`, so it has the same records at the first `n` positions. If `w` is uniform on
`S_N` with `n <= N`, then `recordPrefix n w` is uniform on `S_n`, and the same holds for
independent pairs.
-/

namespace FinitaryPerm

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- Decode the first bounded left inversion coordinates as a supported permutation. -/
noncomputable def recordPrefix (n : ℕ) (w : FinitaryPerm ℕ+) : FinitaryPerm ℕ+ :=
  ((leftCodeEquiv n).symm (leftCoordinates n w)).val

/-- A decoded record prefix is supported in its chosen finite interval. -/
theorem isSupported_recordPrefix (n : ℕ) (w : FinitaryPerm ℕ+) :
    IsSupported n (recordPrefix n w) :=
  ((leftCodeEquiv n).symm (leftCoordinates n w)).property

/-- Decoding a left-coordinate prefix preserves all its bounded coordinates. -/
theorem leftCoordinates_recordPrefix (n : ℕ) (w : FinitaryPerm ℕ+) :
    leftCoordinates n (recordPrefix n w) = leftCoordinates n w := by
  unfold recordPrefix
  rw [leftCoordinates_eq, Equiv.apply_symm_apply]

/-- Prefix decoding fixes a permutation already supported in the prefix interval. -/
theorem recordPrefix_eq {n : ℕ} {w : FinitaryPerm ℕ+} (hw : IsSupported n w) :
    recordPrefix n w = w := by
  have he : (⟨recordPrefix n w, isSupported_recordPrefix n w⟩ :
      {v : FinitaryPerm ℕ+ // IsSupported n v}) = ⟨w, hw⟩ :=
    leftCoordinates_injective n (leftCoordinates_recordPrefix n w)
  exact congrArg Subtype.val he

/-- Every record at a prefix position agrees with the decoded prefix record. -/
theorem isRecord_recordPrefix {n : ℕ} (w : FinitaryPerm ℕ+) (j : ℕ+)
    (hj : (j : ℕ) ≤ n) : IsRecord (recordPrefix n w) j ↔ IsRecord w j := by
  let i : Fin n := ⟨(j : ℕ) - 1, by have := PNat.pos j; omega⟩
  have hi : i.val.succPNat = j := by
    apply PNat.eq
    change (j : ℕ) - 1 + 1 = (j : ℕ)
    have := PNat.pos j
    omega
  rw [←hi, isRecord_iff_leftCoordinate n, isRecord_iff_leftCoordinate n,
    leftCoordinates_recordPrefix]

/-- Taking a left-coordinate prefix of a larger uniform permutation is uniform. -/
theorem map_leftCoordinates_prefix {n N : ℕ} (hn : n ≤ N) :
    (unif (symmetricGroup N)).map (leftCoordinates n) =
      uniformOn (Set.univ : Set (LeftCoordinates n)) := by
  have hi := iIndepFun.precomp (Fin.castLE_injective hn) (iIndepFun_leftCoordinates N)
  have hl := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i : Fin n => (measurable_of_countable
      (fun w : FinitaryPerm ℕ+ => leftCoordinates N w (Fin.castLE hn i))).aemeasurable)).mp hi
  change (unif (symmetricGroup N)).map (leftCoordinates n) = _ at hl
  rw [hl, uniformOn_univ_pi_dep]
  congr 1
  funext i
  exact map_leftCoordinate N (Fin.castLE hn i)

/-- Decoded uniform record prefixes have the uniform law on the smaller symmetric group. -/
theorem map_recordPrefix {n N : ℕ} (hn : n ≤ N) :
    (unif (symmetricGroup N)).map (recordPrefix n) = unif (symmetricGroup n) := by
  let d : LeftCoordinates n → FinitaryPerm ℕ+ := fun c => ((leftCodeEquiv n).symm c).val
  have he : recordPrefix n = d ∘ leftCoordinates n := rfl
  have hm : (unif (symmetricGroup n)).map (recordPrefix n) = unif (symmetricGroup n) := by
    calc
      _ = (unif (symmetricGroup n)).map id := by
        apply Measure.map_congr
        filter_upwards [ae_mem_uniformOn_finset (symmetricGroup n)
          ⟨1, one_mem_symmetricGroup n⟩] with w hw
        exact recordPrefix_eq ((mem_symmetricGroup n w).mp hw)
      _ = _ := Measure.map_id
  rw [he, ←Measure.map_map (measurable_of_countable d)
    (measurable_of_countable (leftCoordinates n)), map_leftCoordinates_prefix hn]
  rw [he, ←Measure.map_map (measurable_of_countable d)
    (measurable_of_countable (leftCoordinates n)), map_leftCoordinates] at hm
  exact hm

end FinitaryPerm

namespace FinitaryPerm

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- A decoded record prefix preserves its non-record indicators at prefix positions. -/
theorem nonRecordIndicator_recordPrefix {n : ℕ} (w : FinitaryPerm ℕ+) (j : ℕ+)
    (hj : (j : ℕ) ≤ n) : (recordPrefix n w).nonRecordIndicator j = w.nonRecordIndicator j := by
  simp only [nonRecordIndicator, isRecord_recordPrefix w j hj]

/-- Independent uniform record prefixes have the smaller independent uniform pair law. -/
theorem map_pair_recordPrefix {n N : ℕ} (hn : n ≤ N) :
    (pairLaw (symmetricGroup N)).map (Prod.map (recordPrefix n) (recordPrefix n)) =
      pairLaw (symmetricGroup n) := by
  rw [pairLaw_eq_prod, ←Measure.map_prod_map _ _
    (measurable_of_countable _) (measurable_of_countable _),
    map_recordPrefix hn, pairLaw_eq_prod]

end FinitaryPerm
