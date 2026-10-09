import SchubertForwardStability.SchubertPolynomials.Stability.ForwardAttainment

/-! # Greatest admissible signed back-stability witness

Finite reversal converts a coordinate moving the first position into one
attaining its ambient forward bound. The longest coefficient symmetry
and insertion formula bound every witness and construct the greatest witness.
-/

namespace SchubertPolynomial

open FinitaryPerm
open scoped Classical

/-- Every admissible witness is bounded by the reversed product support minus the ambient size. -/
theorem backShiftWitness_le_reversed {n : ℕ} {u v : FinitaryPerm ℕ+}
    (hu : IsSupported n u) (hv : IsSupported n v) (h : u ≠ 1 ∨ v ≠ 1)
    {k : ℤ} (hk : BackShiftWitness u v k) :
    k ≤ (productForwardStability (longestElement n * u * longestElement n)
      (longestElement n * v * longestElement n) : ℤ) - (n : ℤ) := by
  obtain ⟨u', v', w, hsu, hsv, hc, hw⟩ := hk
  let m := ((n : ℤ) + k).toNat
  have hu' : IsSupported m u' := hsu.isSupported hu
  have hv' : IsSupported m v' := hsv.isSupported hv
  have hn' : u' ≠ 1 ∨ v' ≠ 1 :=
    h.elim (fun he => Or.inl (fun hh => he (hsu.eq_one_iff.mpr hh)))
      (fun he => Or.inr (fun hh => he (hsv.eq_one_iff.mpr hh)))
  have hm : 1 ≤ m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    rw [hm0] at hu' hv'
    exact hn'.elim (fun he => he ((isSupported_zero_iff u').mp hu'))
      (fun he => he ((isSupported_zero_iff v').mp hv'))
  have hmc : (m : ℤ) = (n : ℤ) + k := by dsimp [m] at hm ⊢; omega
  have hshift : (m : ℤ) - (n : ℤ) = k := by omega
  have heu := conjugate_longest_eq_of_signedShift hu hu' (by rw [hshift]; exact hsu)
  have hev := conjugate_longest_eq_of_signedShift hv hv' (by rw [hshift]; exact hsv)
  let M := max m w.forwardStability
  have hmM : m ≤ M := le_max_left _ _
  have huM := hu'.mono hmM
  have hvM := hv'.mono hmM
  have hwM := w.isSupported_forwardStability.mono (le_max_right m w.forwardStability)
  have hM : 1 ≤ M := hm.trans hmM
  have hcoef : structureConst (longestElement M * u' * longestElement M)
      (longestElement M * v' * longestElement M)
      (longestElement M * w * longestElement M) ≠ 0 := by
    rwa [←structureConst_conjugate_longest M u' v' w huM hvM hwM]
  have hb := forwardStability_le_product hcoef
  rw [forward_conjugate_moves_first hM hwM hw] at hb
  have heF := productForward_conjugate_extend hu' hv' hn' (M - m)
  rw [Nat.add_sub_of_le hmM, ←heu, ←hev] at heF
  rw [heF] at hb
  omega

/-- Reversing a coordinate attaining the forward bound constructs an admissible signed witness. -/
theorem backShiftWitness_reversed_bound {n : ℕ} {u v : FinitaryPerm ℕ+}
    (hu : IsSupported n u) (hv : IsSupported n v) (h : u ≠ 1 ∨ v ≠ 1) :
    BackShiftWitness u v ((productForwardStability
      (longestElement n * u * longestElement n)
      (longestElement n * v * longestElement n) : ℤ) - (n : ℤ)) := by
  let ru := longestElement n * u * longestElement n
  let rv := longestElement n * v * longestElement n
  let F := productForwardStability ru rv
  have hn : ru ≠ 1 ∨ rv ≠ 1 :=
    h.elim (fun he => Or.inl (fun hh => he ((conjugate_longest_eq_one n u).mp hh)))
      (fun he => Or.inr (fun hh => he ((conjugate_longest_eq_one n v).mp hh)))
  have hF : 1 < F := one_lt_productForward ru rv hn
  have hru : IsSupported F ru := ru.isSupported_forwardStability.mono
    (forward_input_le_product_left ru rv)
  have hrv : IsSupported F rv := rv.isSupported_forwardStability.mono
    (forward_input_le_product_right ru rv)
  obtain ⟨w, hc, hwF⟩ := exists_forward_attaining ru rv
  have hw : IsSupported F w := (forwardStability_le_iff w (by omega : 1 ≤ F)).mp
    (le_of_eq hwF)
  refine ⟨longestElement F * ru * longestElement F,
    longestElement F * rv * longestElement F, longestElement F * w * longestElement F,
    ?_, ?_, ?_, ?_⟩
  · exact signedShift_of_conjugate_longest_eq hu hru.conjugate_longest
      (conjugate_longest_twice F ru).symm
  · exact signedShift_of_conjugate_longest_eq hv hrv.conjugate_longest
      (conjugate_longest_twice F rv).symm
  · rwa [←structureConst_conjugate_longest F ru rv w hru hrv hw]
  · apply (conjugate_longest_moves_first (by omega : 1 ≤ F) w).mpr
    have hm := forwardStability_last_moved w (by omega)
    simpa only [hwF] using hm

/-- The intrinsic witness set has greatest element equal to reversed forward support minus size. -/
theorem isGreatest_backShiftWitness {n : ℕ} {u v : FinitaryPerm ℕ+}
    (hu : IsSupported n u) (hv : IsSupported n v) (h : u ≠ 1 ∨ v ≠ 1) :
    IsGreatest {k : ℤ | BackShiftWitness u v k}
      ((productForwardStability (longestElement n * u * longestElement n)
        (longestElement n * v * longestElement n) : ℤ) - (n : ℤ)) :=
  ⟨backShiftWitness_reversed_bound hu hv h, fun _ hk => backShiftWitness_le_reversed hu hv h hk⟩

end SchubertPolynomial
