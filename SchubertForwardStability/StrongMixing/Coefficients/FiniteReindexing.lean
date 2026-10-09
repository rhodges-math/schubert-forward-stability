import SchubertForwardStability.StrongMixing.Coefficients.Reindexing

/-!
# Extending a finite increasing row to integer indices

A strictly increasing finite row is extended linearly below its first value and
above its last value. The extension is strictly increasing on all integers and
agrees with each finite coordinate, including singleton rows.
-/

namespace StrongMixing

/-- Extend a nonempty finite integer row to all integer indices. At negative
indices use the first value plus the index; above `N` use the last value plus
the excess index. In-range values are unchanged. -/
def integerRowExtension {N : ℕ} (e : Fin (N + 1) → ℤ) (i : ℤ) : ℤ :=
  if hi : i < 0 then e 0 + i
  else if hN : i ≤ N then e ⟨i.toNat, by omega⟩
  else e ⟨N, by omega⟩ + (i - N)

/-- The integer extension agrees with every in-range finite coordinate of its
defining row. This includes the first and last coordinates and singleton rows. -/
theorem integerRowExtension_apply {N : ℕ} (e : Fin (N + 1) → ℤ) (i : Fin (N + 1)) :
    integerRowExtension e (i : ℤ) = e i := by
  have h0 : ¬(i : ℤ) < 0 := by omega
  have hN : (i : ℤ) ≤ N := by omega
  simp [integerRowExtension, h0, hN]

/-- If the finite row is strictly increasing, its linear extension
is strictly increasing on all integer indices. No density or consecutive-value
assumption is imposed on the finite row. -/
theorem integerRowExtension_strictMono {N : ℕ} (e : Fin (N + 1) → ℤ)
    (he : StrictMono e) : StrictMono (integerRowExtension e) := by
  have hlo (i : Fin (N + 1)) : e 0 ≤ e i :=
    he.monotone (show (0 : Fin (N + 1)) ≤ i by change 0 ≤ i.val; omega)
  have hhi (i : Fin (N + 1)) : e i ≤ e ⟨N, by omega⟩ :=
    he.monotone (show i ≤ (⟨N, by omega⟩ : Fin (N + 1)) by change i.val ≤ N; omega)
  intro i j hij
  by_cases hi : i < 0
  · by_cases hj : j < 0
    · simp only [integerRowExtension, dite_eq_left hi, dite_eq_left hj]
      omega
    · by_cases hjN : j ≤ N
      · have h := hlo ⟨j.toNat, by omega⟩
        simp only [integerRowExtension, dite_eq_left hi, dite_eq_right hj, dite_eq_left hjN]
        omega
      · have h := hlo ⟨N, by omega⟩
        simp only [integerRowExtension, dite_eq_left hi, dite_eq_right hj, dite_eq_right hjN]
        omega
  · by_cases hiN : i ≤ N
    · by_cases hj : j < 0
      · omega
      · by_cases hjN : j ≤ N
        · have h := he (show (⟨i.toNat, by omega⟩ : Fin (N + 1)) <
              ⟨j.toNat, by omega⟩ by change i.toNat < j.toNat; omega)
          simp only [integerRowExtension, dite_eq_right hi, dite_eq_left hiN,
            dite_eq_right hj, dite_eq_left hjN]
          exact h
        · have h := hhi ⟨i.toNat, by omega⟩
          simp only [integerRowExtension, dite_eq_right hi, dite_eq_left hiN,
            dite_eq_right hj, dite_eq_right hjN]
          omega
    · have hj : ¬j < 0 := by omega
      have hjN : ¬j ≤ N := by omega
      simp only [integerRowExtension, dite_eq_right hi, dite_eq_right hiN,
        dite_eq_right hj, dite_eq_right hjN]
      omega

end StrongMixing
