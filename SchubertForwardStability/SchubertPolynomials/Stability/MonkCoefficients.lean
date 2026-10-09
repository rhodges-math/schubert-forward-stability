import SchubertForwardStability.SchubertPolynomials.Stability.LinearExtraction
import SchubertForwardStability.SchubertPolynomials.Products.Constants

/-! # Schubert coordinates for an initial linear factor

## Main definitions

* `initialCoefficients`: the finite coefficient vector of an initial variable sum.
* `MonkCover`: a length-increasing right transposition crossing the initial boundary.

## Main results

Every coordinate of an initial linear factor times a Schubert polynomial is one
on crossing covers and zero elsewhere. Integer structure constants satisfy the
same formula, derived from divided-difference extraction.
-/

namespace SchubertPolynomial

open FinitaryPerm
open scoped Classical BigOperators

variable {R : Type*} [CommRing R]

/-- The finitely supported vector with coefficient one in the first `n` positions. -/
noncomputable def initialCoefficients (R : Type*) [CommRing R] (n : ℕ) : ℕ+ →₀ R :=
  ∑ j ∈ positions n, Finsupp.single j 1

/-- The initial coefficient vector is the indicator of its positive initial interval. -/
theorem initialCoefficients_apply (n : ℕ) (j : ℕ+) :
    initialCoefficients R n j = if (j : ℕ) ≤ n then 1 else 0 := by
  simp [initialCoefficients, Finsupp.single_apply, mem_positions]

/-- The polynomial of the initial coefficient vector is the initial variable sum. -/
theorem linearForm_initialCoefficients (n : ℕ) :
    linearForm R (initialCoefficients R n) = initialVariableSum R n := by
  simp only [initialCoefficients, map_sum, linearForm_single, one_smul, initialVariableSum]

/-- A positive root contributes one exactly when it crosses the initial boundary. -/
theorem initialCoefficients_difference (n : ℕ) (q r : ℕ+) (hqr : q < r) :
    initialCoefficients R n q - initialCoefficients R n r =
      if (q : ℕ) ≤ n ∧ n < (r : ℕ) then 1 else 0 := by
  by_cases hq : (q : ℕ) ≤ n
  · by_cases hr : n < (r : ℕ)
    · simp only [initialCoefficients_apply, hq, hr, ite_true,
        ite_eq_right (not_le.mpr hr), sub_zero, and_self]
    · simp only [initialCoefficients_apply, hq, not_lt.mp hr, ite_true,
        sub_self, hr, and_false, ite_false]
  · have hr : ¬(r : ℕ) ≤ n := by
      exact not_le.mpr ((not_le.mp hq).trans (show (q : ℕ) < r from hqr))
    simp only [initialCoefficients_apply, ite_eq_right hr,
      sub_self, hq, false_and, ite_false]

/-- A right-transposition cover whose positions cross the initial boundary. -/
def MonkCover (n : ℕ) (u w : FinitaryPerm ℕ+) : Prop :=
  ∃ q r : ℕ+, (q : ℕ) ≤ n ∧ n < (r : ℕ) ∧
    w = u * swap q r ∧ w.length = u.length + 1

private theorem reverse_swap_eq (u w : FinitaryPerm ℕ+) (q r : ℕ+)
    (he : w = u * swap q r) : u = w * swap q r := by
  have hs : (swap q r : FinitaryPerm ℕ+) * swap q r = 1 := by
    simpa only [swap_inv] using mul_inv_cancel (swap q r)
  rw [he, mul_assoc, hs, mul_one]

/-- Initial linear multiplication has exactly the crossing-cover Schubert coordinates. -/
theorem schubertFunctional_initial_mul (n : ℕ) (u w : FinitaryPerm ℕ+) :
    schubertFunctional R w (initialVariableSum R n * schubert R u) =
      if MonkCover n u w then 1 else 0 := by
  rw [← linearForm_initialCoefficients]
  by_cases hl : w.length = u.length + 1
  · by_cases ht : ∃ q r : ℕ+, q < r ∧ u = w * swap q r
    · obtain ⟨q, r, hqr, hu⟩ := ht
      have hw := reverse_swap_eq w u q r hu
      have hc : MonkCover n u w ↔ (q : ℕ) ≤ n ∧ n < (r : ℕ) := by
        constructor
        · rintro ⟨a, b, ha, hb, he, _⟩
          have hab : a < b := by change (a : ℕ) < b; omega
          have hs := swap_ordered_injective hqr hab (mul_left_cancel (hw.symm.trans he))
          simpa only [hs.1, hs.2] using And.intro ha hb
        · intro h
          exact ⟨q, r, h.1, h.2, hw, hl⟩
      have he := schubertFunctional_linear_cover (initialCoefficients R n) w q r hqr
        (by rw [← hu]; omega)
      rw [← hu] at he
      rw [he, initialCoefficients_difference n q r hqr]
      simp only [hc]
    · have hc : ¬ MonkCover n u w := by
        rintro ⟨q, r, hq, hr, he, _⟩
        apply ht
        exact ⟨q, r, (show q < r by change (q : ℕ) < r; omega),
          reverse_swap_eq u w q r he⟩
      rw [ite_eq_right hc]
      apply schubertFunctional_linear_outside _ _ _ hl
      intro q r hqr he
      exact ht ⟨q, r, hqr, he⟩
  · have hc : ¬ MonkCover n u w := by rintro ⟨q, r, _, _, _, he⟩; exact hl he
    rw [ite_eq_right hc]
    exact schubertFunctional_linear_off_length _ _ _ hl

/-- Multiplication by a simple Schubert polynomial has the Monk cover coefficients. -/
theorem structureCoefficients_simple (i : ℕ+) (u w : FinitaryPerm ℕ+) :
    structureCoefficients R (simpleTransposition i) u w =
      if MonkCover (i : ℕ) u w then 1 else 0 := by
  rw [structureCoefficients_apply, schubert_simpleTransposition]
  exact schubertFunctional_initial_mul (i : ℕ) u w

/-- Integer multiplication by a simple Schubert polynomial has the Monk cover coefficients. -/
theorem structureConst_simple (i : ℕ+) (u w : FinitaryPerm ℕ+) :
    structureConst (simpleTransposition i) u w =
      if MonkCover (i : ℕ) u w then 1 else 0 := by
  rw [structureConst_eq_functional, schubert_simpleTransposition]
  exact schubertFunctional_initial_mul (i : ℕ) u w

/-- The integer Monk coefficients are nonnegative. -/
theorem structureConst_simple_nonneg (i : ℕ+) (u w : FinitaryPerm ℕ+) :
    0 ≤ structureConst (simpleTransposition i) u w := by
  rw [structureConst_simple]
  split_ifs <;> omega

/-- The integer Monk support consists exactly of the crossing covers. -/
theorem structureConst_simple_ne_zero (i : ℕ+) (u w : FinitaryPerm ℕ+) :
    structureConst (simpleTransposition i) u w ≠ 0 ↔ MonkCover (i : ℕ) u w := by
  rw [structureConst_simple]
  split_ifs <;> simp_all

/-- The crossing-cover output set is finite. -/
theorem monkCover_finite (i : ℕ+) (u : FinitaryPerm ℕ+) :
    Set.Finite {w | MonkCover (i : ℕ) u w} := by
  exact (structureConst_finite_support (simpleTransposition i) u).subset
    (fun w hw => (structureConst_simple_ne_zero i u w).mpr hw)

/-- The finite set of right-transposition covers crossing a positive boundary. -/
noncomputable def monkCovers (i : ℕ+) (u : FinitaryPerm ℕ+) :
    Finset (FinitaryPerm ℕ+) := (monkCover_finite i u).toFinset

/-- Membership in the finite crossing-cover set is given by its transposition
condition. -/
theorem mem_monkCovers (i : ℕ+) (u w : FinitaryPerm ℕ+) :
    w ∈ monkCovers i u ↔ MonkCover (i : ℕ) u w := Set.Finite.mem_toFinset _

/-- Monk's finite expansion by precisely the crossing covers, over every commutative ring. -/
theorem monk_expansion (i : ℕ+) (u : FinitaryPerm ℕ+) :
    (∑ w ∈ monkCovers i u, schubert R w) =
      initialVariableSum R (i : ℕ) * schubert R u := by
  have hs : (structureCoefficients R (simpleTransposition i) u).support ⊆ monkCovers i u := by
    intro w hw
    apply (mem_monkCovers i u w).mpr
    have hn := Finsupp.mem_support_iff.mp hw
    rw [structureCoefficients_simple] at hn
    by_contra hc
    exact hn (ite_eq_right hc)
  calc
    (∑ w ∈ monkCovers i u, schubert R w) =
        ∑ w ∈ monkCovers i u, structureCoefficients R (simpleTransposition i) u w •
          schubert R w := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [structureCoefficients_simple, ite_eq_left ((mem_monkCovers i u w).mp hw), one_smul]
    _ = ∑ w ∈ (structureCoefficients R (simpleTransposition i) u).support,
        structureCoefficients R (simpleTransposition i) u w • schubert R w := by
      symm
      apply Finset.sum_subset hs
      intro w hw hn
      rw [Finsupp.notMem_support_iff.mp hn, zero_smul]
    _ = initialVariableSum R (i : ℕ) * schubert R u := by
      rw [schubert_mul_expansion, schubert_simpleTransposition]
      rfl

end SchubertPolynomial
