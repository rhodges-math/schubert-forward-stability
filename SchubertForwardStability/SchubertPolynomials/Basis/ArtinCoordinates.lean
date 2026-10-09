import SchubertForwardStability.SchubertPolynomials.Basis.ArtinSpan
import SchubertForwardStability.Permutations.Finitary.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Finite coordinates for Artin exponents

## Main definitions

* `ArtinCoordinates n` consists of coordinates in `Fin (n - i)` for `i : Fin n`.
* `artinExponentEquiv n` identifies these coordinates with Artin-bounded exponents.

## Main results

* `card_artinExponent` counts Artin-bounded exponents as `n!`.

## Implementation notes

Finite coordinate `i` corresponds to positive variable index `i + 1`. The equivalence
extends a finite coordinate function by zero beyond the ambient size.

## References

* I. G. Macdonald, *Notes on Schubert polynomials*, Chapter IV.
-/

namespace SchubertPolynomial

noncomputable section

open scoped BigOperators

/-- Finite exponent coordinates with staircase bounds, indexed from zero. -/
abbrev ArtinCoordinates (n : ℕ) := (i : Fin n) → Fin (n - i.val)

private def coordinateExponent (n : ℕ) (b : ArtinCoordinates n) : ℕ+ →₀ ℕ :=
  Finsupp.onFinset (FinitaryPerm.positions n)
    (fun j => if hj : (j : ℕ) ≤ n then
      (b ⟨(j : ℕ) - 1, by have := PNat.pos j; omega⟩).val else 0) fun j hj => by
        rw [FinitaryPerm.mem_positions]
        by_contra h
        simp only [dite_eq_right h] at hj
        exact hj rfl

private theorem coordinateExponent_apply (n : ℕ) (b : ArtinCoordinates n) (j : ℕ+) :
    coordinateExponent n b j = if hj : (j : ℕ) ≤ n then
      (b ⟨(j : ℕ) - 1, by have := PNat.pos j; omega⟩).val else 0 := rfl

private theorem coordinateExponent_bounded (n : ℕ) (b : ArtinCoordinates n) :
    IsArtinExponent n (coordinateExponent n b) := by
  intro j
  rw [coordinateExponent_apply]
  split_ifs with hj
  · have hjpos := PNat.pos j
    have hb := (b ⟨(j : ℕ) - 1, by omega⟩).isLt
    change (b ⟨(j : ℕ) - 1, _⟩).val < n - ((j : ℕ) - 1) at hb
    change (b ⟨(j : ℕ) - 1, _⟩).val ≤ n - (j : ℕ)
    omega
  · exact Nat.zero_le _

/-- Artin-bounded exponent vectors are equivalent to their finite staircase coordinates. -/
def artinExponentEquiv (n : ℕ) :
    {a : ℕ+ →₀ ℕ // IsArtinExponent n a} ≃ ArtinCoordinates n where
  toFun a i := ⟨a.1 (Nat.succPNat i.val), by
    have hi := i.isLt
    have ha := a.2 (Nat.succPNat i.val)
    change a.1 (Nat.succPNat i.val) ≤ n - (i.val + 1) at ha
    omega⟩
  invFun b := ⟨coordinateExponent n b, coordinateExponent_bounded n b⟩
  left_inv a := by
    apply Subtype.ext
    ext j
    rw [coordinateExponent_apply]
    split_ifs with hj
    · change a.1 (Nat.succPNat ((j : ℕ) - 1)) = a.1 j
      congr 1
      apply PNat.eq
      have hjpos := PNat.pos j
      change (j : ℕ) - 1 + 1 = (j : ℕ)
      omega
    · have ha := a.2 j
      omega
  right_inv b := by
    funext i
    apply Fin.ext
    change coordinateExponent n b (Nat.succPNat i.val) = (b i).val
    rw [coordinateExponent_apply,
      dite_eq_left (by have hi := i.isLt; change i.val + 1 ≤ n; omega)]
    change (b ⟨i.val + 1 - 1, _⟩).val = (b i).val
    congr 1

/-- Artin exponent coordinates read the exponent at the corresponding positive index. -/
@[simp] theorem artinExponentEquiv_apply (n : ℕ)
    (a : {a : ℕ+ →₀ ℕ // IsArtinExponent n a}) (i : Fin n) :
    (artinExponentEquiv n a i).val = a.1 (Nat.succPNat i.val) := rfl

/-- The bounded Artin exponent vectors form a finite type. -/
instance fintypeArtinExponent (n : ℕ) :
    Fintype {a : ℕ+ →₀ ℕ // IsArtinExponent n a} :=
  Fintype.ofEquiv (ArtinCoordinates n) (artinExponentEquiv n).symm

/-- The finite staircase coordinate functions are counted by the factorial. -/
theorem card_artinCoordinates (n : ℕ) : Fintype.card (ArtinCoordinates n) = n.factorial := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [Finset.prod_fin_eq_prod_range]
  calc
    _ = ∏ i ∈ Finset.range n, (n - i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [dite_eq_left (Finset.mem_range.mp hi)]
    _ = n.factorial := by
      rw [← Finset.prod_range_reflect (fun i => n - i) n]
      rw [Nat.factorial_eq_prod_range_add_one]
      apply Finset.prod_congr rfl
      intro i hi
      have hin := Finset.mem_range.mp hi
      omega

/-- There are exactly `n!` Artin-bounded exponent vectors. -/
theorem card_artinExponent (n : ℕ) :
    Fintype.card {a : ℕ+ →₀ ℕ // IsArtinExponent n a} = n.factorial :=
  (Fintype.card_congr (artinExponentEquiv n)).trans (card_artinCoordinates n)

end

end SchubertPolynomial
