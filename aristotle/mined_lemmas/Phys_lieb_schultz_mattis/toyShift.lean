/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
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

/-!
## Setting

We formalise the Lieb–Schultz–Mattis (LSM) theorem in its finite-volume, variational form
(Lieb–Schultz–Mattis 1961, Affleck–Lieb 1986, Oshikawa 2000).

For each system size `L` we have a finite dimensional complex Hilbert space `E L`
(the state space of a chain of `L` sites), a self-adjoint Hamiltonian `Ham L`, and a
unitary translation operator `Tr L`.  The two physical inputs of LSM are:

* the ground state `ψ₀ L` is a translation eigenstate, `Tr L ψ₀ = ω • ψ₀` with `‖ω‖ = 1`
  (its momentum);
* for a chain with **half-integer spin per unit cell** the Lieb–Schultz–Mattis twist
  `ψ₁ L = U_twist ψ₀ L` is a normalised state whose momentum is shifted by exactly `π`,
  i.e. `Tr L ψ₁ = (-ω) • ψ₁`, and whose energy exceeds the ground energy by at most
  `C / L` (the twist is a low-energy variational state).

The theorem proved below is that these inputs are incompatible with the chain having,
for every size, a *unique* ground state separated from the rest of the spectrum by a
gap `γ > 0` that does not shrink with `L`.  In other words the chain is gapless or its
ground state is degenerate.
-/

namespace Phys

open Module

section Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The energy (expectation value of the Hamiltonian `H`) of a state `ψ`. -/

noncomputable def toyShift : EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i => if i = 0 then LinearIsometryEquiv.refl ℂ ℂ else LinearIsometryEquiv.neg ℂ)

/-- **Non-vacuity.**  The hypotheses of `lieb_schultz_mattis` are satisfiable, so the theorem
is not vacuously true. -/
