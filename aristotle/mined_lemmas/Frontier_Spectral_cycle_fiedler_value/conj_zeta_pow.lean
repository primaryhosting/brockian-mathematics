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

lemma conj_zeta_pow (hn : n ≠ 0) (s : ℕ) :
    (starRingEnd ℂ) (zeta n ^ s) = zeta n ^ ((n - 1) * s) := by
  have hns : Complex.normSq (zeta n) = 1 := by simpa using normSq_zeta_pow (k := 1) hn
  have h1 : zeta n * (starRingEnd ℂ) (zeta n) = 1 := by
    rw [Complex.mul_conj, hns]
    norm_num
  have h2 : zeta n * zeta n ^ (n - 1) = 1 := by
    rw [← pow_succ']
    have hnn : (n - 1) + 1 = n := by omega
    rw [hnn, zeta_pow_self hn]
  have hbase : (starRingEnd ℂ) (zeta n) = zeta n ^ (n - 1) :=
    mul_left_cancel₀ zeta_ne_zero (h1.trans h2.symm)
  rw [map_pow, hbase, ← pow_mul]

