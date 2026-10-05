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

theorem isPrimeB_sound {n : Nat} (hn : n ≤ 2024) (h : isPrimeB n = true) : IsPrimeNat n := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hnd⟩ := h
  refine isPrimeNat_of_noDivBelow h2 ?_ hnd
  unfold trialBound
  rcases Nat.lt_or_ge 45 n with hlt | hle
  · rw [if_neg (by omega)]
    omega
  · rw [if_pos hle]
    have hn1 : n - 1 + 1 = n := by omega
    rw [hn1]
    have hsq : 2 * n ≤ n * n := Nat.mul_le_mul_right n h2
    omega

/-! ## The Goldbach property -/

/-- `GoldbachK2 n` : `n` is a sum of two (not necessarily distinct) primes. -/
