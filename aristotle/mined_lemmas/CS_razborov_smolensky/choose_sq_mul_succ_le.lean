import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem choose_sq_mul_succ_le (n i : ℕ) : (n.choose i) ^ 2 * (n + 1) ≤ 2 * 4 ^ n := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have hmid : (m + m).choose i ≤ Nat.centralBinom m := by
      have := Nat.choose_le_middle i (m + m)
      rw [Nat.centralBinom, show 2 * m = m + m by ring]
      simpa [show (m + m) / 2 = m by omega] using this
    calc ((m + m).choose i) ^ 2 * (m + m + 1)
        ≤ (Nat.centralBinom m) ^ 2 * (3 * m + 1) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hmid 2) (by omega)
      _ ≤ 16 ^ m := centralBinom_sq_le m
      _ ≤ 2 * 4 ^ (m + m) := by
          rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul, show 2 * m = m + m by ring]
          omega
  · subst hm
    have hmid : (2 * m + 1).choose i ≤ 2 * Nat.centralBinom m := by
      have h1 : (2 * m + 1).choose i ≤ (2 * m + 1).choose m := by
        have := Nat.choose_le_middle i (2 * m + 1)
        simpa [Nat.add_mul_div_left, Nat.mul_add_div] using this
      have hsym : (2 * m + 1).choose m = (2 * m + 1).choose (m + 1) := by
        rw [← Nat.choose_symm (by omega)]; congr 1; omega
      have hp : (2 * m + 1).choose (m + 1) = (2 * m).choose m + (2 * m).choose (m + 1) := by
        rw [show 2 * m + 1 = 2 * m + 1 by ring, Nat.choose_succ_succ']
      have h2 : (2 * m).choose (m + 1) ≤ (2 * m).choose m := by
        have := Nat.choose_le_middle (m + 1) (2 * m)
        simpa [Nat.mul_div_cancel_left] using this
      rw [Nat.centralBinom]
      omega
    calc ((2 * m + 1).choose i) ^ 2 * (2 * m + 1 + 1)
        ≤ (2 * Nat.centralBinom m) ^ 2 * (2 * (3 * m + 1)) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hmid 2) (by omega)
      _ = 8 * ((Nat.centralBinom m) ^ 2 * (3 * m + 1)) := by ring
      _ ≤ 8 * 16 ^ m := Nat.mul_le_mul_left _ (centralBinom_sq_le m)
      _ = 2 * 4 ^ (2 * m + 1) := by
          rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul, pow_succ]; ring

/-- The sum of the binomial coefficients `C(2m+1, i)` for `i ≤ m + D`. -/
