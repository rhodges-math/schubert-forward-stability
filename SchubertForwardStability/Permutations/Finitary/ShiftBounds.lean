import SchubertForwardStability.Permutations.Finitary.PositiveShift
import Mathlib.Tactic

/-! # Support bounds under positive shifts

Shifting a permutation supported in `[1, n]` by `m` gives a permutation supported in
`[1, m+n]`.
-/

namespace FinitaryPerm

/-- Shifting a permutation supported in n places gives support in m+n places. -/
theorem shiftPermHom_supported (m n : ℕ) (w : FinitaryPerm ℕ+)
    (hw : IsSupported n w) : IsSupported (m + n) (shiftPermHom m w) := by
  intro i hi
  let j : ℕ+ := ⟨(i : ℕ) - m, by omega⟩
  have hIndex : shiftPosition m j = i := by
    apply PNat.eq
    change m + ((i : ℕ) - m) = (i : ℕ)
    omega
  rw [← hIndex, shiftPermHom_apply, hw j (by change n < (i : ℕ) - m; omega)]

end FinitaryPerm
