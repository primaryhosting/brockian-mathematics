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

lemma zeta_geom_sum (hn : n ≠ 0) (t : ℕ) :
    ∑ k ∈ Finset.range n, (zeta n ^ t) ^ k = if n ∣ t then (n : ℂ) else 0 := by
  by_cases h : n ∣ t
  · rw [if_pos h]
    have h1 : zeta n ^ t = 1 := ((isPrimitiveRoot_zeta hn).pow_eq_one_iff_dvd t).mpr h
    simp [h1]
  · rw [if_neg h]
    have hne : zeta n ^ t ≠ 1 := fun hh => h (((isPrimitiveRoot_zeta hn).pow_eq_one_iff_dvd t).mp hh)
    rw [geom_sum_eq hne]
    have hpow : (zeta n ^ t) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, zeta_pow_self hn, one_pow]
    rw [hpow]
    simp

