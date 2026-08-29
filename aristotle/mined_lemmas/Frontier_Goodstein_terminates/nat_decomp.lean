import Mathlib
/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open Ordinal

/-! ### Arithmetic preliminaries -/


theorem nat_decomp (c e q s : ℕ) (hc : 2 ≤ c) (hq0 : 0 < q) (hqc : q < c) (hs : s < c ^ e) :
    Nat.log c (c ^ e * q + s) = e ∧ (c ^ e * q + s) / c ^ e = q ∧ (c ^ e * q + s) % c ^ e = s := by
  have hce : 0 < c ^ e := Nat.pow_pos (lt_of_lt_of_le Nat.zero_lt_two hc)
  have hdiv : (c ^ e * q + s) / c ^ e = q := by
    rw [Nat.mul_add_div hce, Nat.div_eq_of_lt hs, Nat.add_zero]
  have hmod : (c ^ e * q + s) % c ^ e = s := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
  refine ⟨?_, hdiv, hmod⟩
  have hlow : c ^ e ≤ c ^ e * q + s := le_trans (Nat.le_mul_of_pos_right _ hq0) (Nat.le_add_right _ _)
  have hhigh : c ^ e * q + s < c ^ (e + 1) := by
    have : c ^ e * q + s < c ^ e * q + c ^ e := by omega
    calc c ^ e * q + s < c ^ e * q + c ^ e := this
      _ = c ^ e * (q + 1) := by ring
      _ ≤ c ^ e * c := Nat.mul_le_mul_left _ hqc
      _ = c ^ (e + 1) := by ring
  exact Nat.log_eq_of_pow_le_of_lt_pow hlow hhigh

/-- Casting a natural power into the ordinals. -/
