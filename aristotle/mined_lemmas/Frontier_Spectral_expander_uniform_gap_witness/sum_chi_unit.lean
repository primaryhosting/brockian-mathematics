import Mathlib
/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`
(there are `2 ^ k` of them). -/
abbrev Cube (k : ℕ) : Type := Fin k → ZMod 2


theorem sum_chi_unit {k : ℕ} (S : Finset (Fin k)) :
    ∑ i : Fin k, chi S (unit i) = (k : ℝ) - 2 * S.card := by
  have h : ∀ i : Fin k, chi S (unit i) = 1 - 2 * (if i ∈ S then (1 : ℝ) else 0) := by
    intro i; rw [chi_unit]; split <;> ring
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h i), Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  simp

/-- The Laplacian acts on functions by `L v x = k * v x - ∑ i, v (x + e i)`. -/
