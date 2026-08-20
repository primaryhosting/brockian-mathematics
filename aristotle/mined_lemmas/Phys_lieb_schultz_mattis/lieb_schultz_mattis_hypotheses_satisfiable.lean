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

theorem lieb_schultz_mattis_hypotheses_satisfiable :
    ∃ (Ham : ∀ _L : ℕ, EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))
      (Tr : ∀ _L : ℕ, EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2))
      (ψ₀ ψ₁ : ∀ _L : ℕ, EuclideanSpace ℂ (Fin 2)) (E₀ : ℕ → ℝ) (ω : ℕ → ℂ) (C : ℝ),
      (∀ L, ‖ω L‖ = 1) ∧ (∀ L, Tr L (ψ₀ L) = ω L • ψ₀ L) ∧
        (∀ L, Tr L (ψ₁ L) = (-(ω L)) • ψ₁ L) ∧ (∀ L, ‖ψ₁ L‖ = 1) ∧
        (∀ L, 0 < L → energy (Ham L) (ψ₁ L) ≤ E₀ L + C / L) := by
  refine ⟨fun _ => 0, fun _ => toyShift, fun _ => EuclideanSpace.single 0 1,
    fun _ => EuclideanSpace.single 1 1, fun _ => 0, fun _ => 1, 0, fun L => by simp, ?_, ?_, ?_, ?_⟩
  · intro L
    ext i
    fin_cases i <;>
      simp [toyShift, LinearIsometryEquiv.piLpCongrRight_apply, EuclideanSpace.single_apply]
  · intro L
    ext i
    fin_cases i <;>
      simp [toyShift, LinearIsometryEquiv.piLpCongrRight_apply, EuclideanSpace.single_apply]
  · intro L
    simp
  · intro L _
    simp [energy]

/-- A two-level toy Hamiltonian: it annihilates the first basis vector and acts as the
identity on the second.  Used only to certify that `GappedGroundState` is satisfiable. -/
