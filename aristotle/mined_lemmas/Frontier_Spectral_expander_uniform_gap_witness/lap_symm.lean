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


theorem lap_symm {k : ℕ} (v w : Cube k → ℝ) :
    ∑ x : Cube k, ((hypercube k).lapMatrix ℝ).mulVec v x * w x
      = ∑ x : Cube k, v x * ((hypercube k).lapMatrix ℝ).mulVec w x := by
  have shift : ∀ u : Cube k, ∑ x : Cube k, v (x + u) * w x
      = ∑ x : Cube k, v x * w (x + u) := by
    intro u
    refine Fintype.sum_equiv (Equiv.addRight u) _ _ ?_
    intro x
    simp only [Equiv.coe_addRight]
    rw [add_assoc, cube_add_self, add_zero]
  have expand : ∑ x : Cube k, ((hypercube k).lapMatrix ℝ).mulVec v x * w x
      = (k : ℝ) * (∑ x : Cube k, v x * w x)
        - ∑ i : Fin k, ∑ x : Cube k, v (x + unit i) * w x := by
    have hx : ∀ x : Cube k, ((hypercube k).lapMatrix ℝ).mulVec v x * w x
        = (k : ℝ) * (v x * w x) - ∑ i : Fin k, v (x + unit i) * w x := by
      intro x
      rw [lap_apply, sub_mul, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_comm]
  have expand2 : ∑ x : Cube k, v x * ((hypercube k).lapMatrix ℝ).mulVec w x
      = (k : ℝ) * (∑ x : Cube k, v x * w x)
        - ∑ i : Fin k, ∑ x : Cube k, v x * w (x + unit i) := by
    have hx : ∀ x : Cube k, v x * ((hypercube k).lapMatrix ℝ).mulVec w x
        = (k : ℝ) * (v x * w x) - ∑ i : Fin k, v x * w (x + unit i) := by
      intro x
      rw [lap_apply, mul_sub, Finset.mul_sum]
      ring_nf
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_comm]
  rw [expand, expand2]
  congr 1
  exact Finset.sum_congr rfl fun i _ => shift (unit i)

/-- Fourier inversion on the hypercube. -/
