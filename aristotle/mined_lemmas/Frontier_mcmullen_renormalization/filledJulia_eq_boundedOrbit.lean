/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
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

namespace Frontier

/-! ## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard; the basic object of McMullen's work on
renormalization) is a holomorphic proper degree-two branched cover `f : U → V`
between open subsets of `ℂ` with `U` compactly contained in `V`.  The
degree-two condition is encoded concretely below: there is one critical value,
whose fiber is a single point, and every other value has exactly two
preimages. -/

/-- The quadratic family `z ↦ z ^ 2 + c`. -/

theorem filledJulia_eq_boundedOrbit (hR : 1 < R) (hRc : R + ‖c‖ < R ^ 2) :
    filledJulia (qmap c) R = boundedOrbit (qmap c) := by
  ext z
  constructor
  · intro hz; exact ⟨R, hz⟩
  · intro hz n
    by_contra hcon
    push_neg at hcon
    have hmem : (qmap c)^[n] z ∈ boundedOrbit (qmap c) := by
      obtain ⟨M, hM⟩ := hz
      refine ⟨M, fun m => ?_⟩
      rw [← Function.iterate_add_apply]
      exact hM (m + n)
    exact unbounded_of_escape hR hRc hcon hmem

/-- The filled Julia set is closed. -/
