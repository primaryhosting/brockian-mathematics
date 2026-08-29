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

lemma zeta_orthogonality (hn : n ≠ 0) (j l : Fin n) :
    ∑ k ∈ Finset.range n, zeta n ^ (j.val * k) * (starRingEnd ℂ) (zeta n ^ (l.val * k))
      = if j = l then (n : ℂ) else 0 := by
  have hterm : ∀ k, zeta n ^ (j.val * k) * (starRingEnd ℂ) (zeta n ^ (l.val * k))
      = (zeta n ^ (j.val + (n - 1) * l.val)) ^ k := by
    intro k
    rw [conj_zeta_pow hn, ← pow_add, ← pow_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), zeta_geom_sum hn]
  simp only [dvd_shift_iff hn]

/-- Discrete Fourier transform of a real vector indexed by `Fin n`. -/
