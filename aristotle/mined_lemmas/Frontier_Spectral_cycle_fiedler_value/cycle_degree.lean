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

lemma cycle_degree (hm : 2 ≤ m) (i : Fin (m + 1)) : (cycleGraph (m + 1)).degree i = 2 := by
  have h := cycle_sum_adj hm (fun _ => (1 : ℝ)) i
  rw [← Finset.sum_filter] at h
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h.trans (by norm_num : (1 : ℝ) + 1 = 2)

/-- The Laplacian of the cycle graph acts as the discrete second difference. -/
