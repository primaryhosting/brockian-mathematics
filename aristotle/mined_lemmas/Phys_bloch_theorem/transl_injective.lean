/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Statement: Eigenstates of a periodic Hamiltonian are Bloch waves e^{ikx}u_k(x).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace Phys

/-- Translation of a wave function by the lattice constant `a`: `(transl a f) x = f (x + a)`. -/

lemma transl_injective (A : ℝ) : Function.Injective (transl A) := by
  intro f g h
  funext x
  have := congrFun h (x - A)
  simpa [transl] using this

/-- The hypotheses of `bloch_theorem` are satisfiable: they hold for the plane wave
`ψ x = e^{ix}` with lattice constant `2π`, so the theorem is not vacuous. -/
