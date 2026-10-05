import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
-- `open scoped Classical` is omitted here: it overrides the graph's own `DecidableRel`
-- instances and makes `if`-congruence rewriting fail below.
-- open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open SimpleGraph Matrix Finset

section Combinatorics

variable {m : ℕ}

/-- Adjacency in the cycle graph on `Fin (m+1)` (with `m ≥ 2`) in additive form. -/

lemma succ_ne_pred (hm : 2 ≤ m) (i : Fin (m + 1)) : i + 1 ≠ i - 1 := by
  have h1 : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  intro h
  have h2 : (1 : Fin (m + 1)) + 1 = 0 := by
    have hc : i + ((1 : Fin (m + 1)) + 1) = i + 0 := by
      rw [← add_assoc, h, add_zero, sub_add_cancel]
    exact add_left_cancel hc
  have h3 := congrArg Fin.val h2
  rw [Fin.val_add, h1, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at h3
  omega

/-- Summing a function against the adjacency relation of the cycle graph. -/
