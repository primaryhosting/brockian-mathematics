/-
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
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

namespace QPhys

/-!
## The Fock space model of the quantum harmonic oscillator

We realise the state space of the one-dimensional quantum harmonic oscillator as the
(algebraic) Fock space `ℕ →₀ ℂ`, whose canonical basis vector `Finsupp.single n 1`
represents the `n`-th number state `|n⟩`.

The ladder operators are defined on this basis by the usual formulas
`a |n⟩ = √n |n-1⟩` and `a† |n⟩ = √(n+1) |n+1⟩`; we check the canonical commutation
relation `[a, a†] = 1`, build the number operator `N = a† a` and the Hamiltonian
`H = ℏω (N + ½)`, and finally compute the set of eigenvalues of `H` to be exactly
`{ℏω(n + ½) : n ∈ ℕ}`.
-/

/-- The annihilation (lowering) operator `a`, determined by `a |n⟩ = √n |n-1⟩`. -/

theorem ladder_commutator :
    ladderDown ∘ₗ ladderUp - ladderUp ∘ₗ ladderDown = LinearMap.id := by
  refine LinearMap.ext fun v => Finsupp.ext fun m => ?_
  have hN : (ladderUp (ladderDown v)) m = (m : ℂ) * v m := numberOp_apply v m
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply,
    Finsupp.sub_apply, ladderDown_ladderUp_apply, hN]
  ring

/-- The Hamiltonian of the quantum harmonic oscillator, `H = ℏω (a† a + ½)`. -/
