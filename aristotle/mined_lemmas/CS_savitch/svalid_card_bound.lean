/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a module docstring: Lean 4 requires `import` lines to come
first, so the very first comment of the file cannot be a module docstring.)

This file develops space bounded machines, proves Savitch's theorem
`NSPACE f ⊆ DSPACE (f ^ 2)` and deduces `PSPACE = NPSPACE`.
-/

set_option autoImplicit false

namespace CS

/-! ## Languages -/

/-- A language is a predicate on binary strings. -/
abbrev Language := List Bool → Prop

/-- The bit of `x` at position `i` (`false` beyond the end of `x`). -/

theorem svalid_card_bound {N K s : ℕ} (hN : N ≤ 2 ^ s) (hK : K = s + 1) :
    3 * ((N + 1) * ((N + 1) * ((K + 1) * ((N + 2) * 2))) + 1) ^ (K + 1)
      ≤ 2 ^ (6 * (s + 2) ^ 2) := by
  have hp : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
  have h1 : N + 1 ≤ 2 ^ (s + 1) := by
    have : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by rw [pow_succ]; ring
    omega
  have h2 : N + 2 ≤ 2 ^ (s + 2) := by
    have : 2 ^ (s + 2) = 2 ^ s + 2 ^ s + 2 ^ s + 2 ^ s := by rw [pow_succ, pow_succ]; ring
    omega
  have h3 : K + 1 ≤ 2 ^ (s + 2) := by
    rw [hK]
    exact le_of_lt Nat.lt_two_pow_self
  have hM : (N + 1) * ((N + 1) * ((K + 1) * ((N + 2) * 2))) ≤ 2 ^ (4 * s + 7) := by
    have : (2:ℕ) ^ (s+1) * (2 ^ (s+1) * (2 ^ (s+2) * (2 ^ (s+2) * 2))) = 2 ^ (4 * s + 7) := by
      rw [← pow_succ, ← pow_add, ← pow_add, ← pow_add]
      ring_nf
    calc (N + 1) * ((N + 1) * ((K + 1) * ((N + 2) * 2)))
        ≤ 2 ^ (s+1) * (2 ^ (s+1) * (2 ^ (s+2) * (2 ^ (s+2) * 2))) := by
          gcongr
      _ = 2 ^ (4 * s + 7) := this
  have hM1 : (N + 1) * ((N + 1) * ((K + 1) * ((N + 2) * 2))) + 1 ≤ 2 ^ (4 * s + 8) := by
    have hq : (1 : ℕ) ≤ 2 ^ (4 * s + 7) := Nat.one_le_two_pow
    have : 2 ^ (4 * s + 8) = 2 ^ (4 * s + 7) + 2 ^ (4 * s + 7) := by rw [pow_succ]; ring
    omega
  calc 3 * ((N + 1) * ((N + 1) * ((K + 1) * ((N + 2) * 2))) + 1) ^ (K + 1)
      ≤ 2 ^ 2 * (2 ^ (4 * s + 8)) ^ (K + 1) := by
        gcongr
        · norm_num
    _ = 2 ^ (2 + (4 * s + 8) * (s + 2)) := by
        rw [← pow_mul, ← pow_add, hK]
    _ ≤ 2 ^ (6 * (s + 2) ^ 2) := by
        apply Nat.pow_le_pow_right (by norm_num)
        nlinarith [sq_nonneg s]

/-- There are at most `2 ^ (6 * (s + 2) ^ 2)` valid states when `N ≤ 2 ^ s` and `K = s + 1`. -/
