import Mathlib
import RequestProject.GoldbachWheelK2_947

/-!
# Goldbach Wheel K 2 947 — Mathlib interface

The target theorem `Brockian.GoldbachWheelK2_947` lives in the self-contained file
`RequestProject/GoldbachWheelK2_947.lean` (which carries no imports, since its header
comment must be the first thing in the file). Here we identify the primality notion used
there with Mathlib's `Nat.Prime` and restate the result in Mathlib terms.
-/

namespace Brockian

/-- The self-contained primality predicate agrees with Mathlib's `Nat.Prime`. -/

theorem isPrimeNat_of_noDivBelow {n k : Nat} (h2 : 2 ≤ n) (hk : n < (k + 1) * (k + 1))
    (h : noDivBelow n k = true) : IsPrimeNat n := by
  refine ⟨h2, ?_⟩
  intro d hd
  rcases Classical.em (d = 1) with h1 | hd1
  · exact Or.inl h1
  rcases Classical.em (d = n) with h1 | hdn
  · exact Or.inr h1
  exfalso
  obtain ⟨e, he⟩ := hd
  subst he
  have hd0 : d ≠ 0 := by rintro rfl; rw [Nat.zero_mul] at h2; omega
  have he0 : e ≠ 0 := by rintro rfl; rw [Nat.mul_zero] at h2; omega
  have he1 : e ≠ 1 := by rintro rfl; rw [Nat.mul_one] at hdn; exact hdn rfl
  have hd2 : 2 ≤ d := by omega
  have he2 : 2 ≤ e := by omega
  have key : ∀ a b : Nat, 2 ≤ a → a ≤ b → a * b < (k + 1) * (k + 1) →
      noDivBelow (a * b) k = true → False := by
    intro a b ha hab hlt hnd
    have hsq : a * a ≤ a * b := Nat.mul_le_mul_left a hab
    have hak : a ≤ k := by
      rcases Nat.lt_or_ge k a with hh | hh
      · have : (k + 1) * (k + 1) ≤ a * a := Nat.mul_le_mul (by omega) (by omega)
        omega
      · exact hh
    exact noDivBelow_sound hnd a ha hak (Nat.dvd_iff_mod_eq_zero.mp ⟨b, rfl⟩)
  rcases Nat.le_total d e with hle | hle
  · exact key d e hd2 hle hk h
  · exact key e d he2 hle (by rw [Nat.mul_comm]; exact hk) (by rw [Nat.mul_comm]; exact h)

/-- How far to trial divide: up to `44` (enough for `n < 45^2 = 2025`), but never beyond
`n - 1`, so that the test is also correct for small `n`. -/
