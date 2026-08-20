import Mathlib

/-!
# Quantum relative entropy and data processing

This file develops, for finite-dimensional systems (complex matrices), the basic theory of the
Umegaki quantum relative entropy

`D(ρ‖σ) = Tr(ρ log ρ) - Tr(ρ log σ)`

for faithful (positive definite) density matrices, together with

* Klein's inequality `QI.relEntropy_nonneg` : `0 ≤ D(ρ‖σ)`;
* invariance under unitary channels `QI.relEntropy_unitary_conj`;
* the data-processing inequality `QI.data_processing_condExp` for trace-self-adjoint maps fixing `σ`
  (conditional expectations), and its concrete instance for the completely dephasing channel
  `QI.data_processing_dephasing`.
-/

open Matrix
open scoped ComplexOrder

namespace QI

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The logarithm of a (Hermitian) matrix, defined through the continuous functional calculus. -/

theorem data_processing_measure_eigenbasis {ρ σ : Matrix n n ℂ} (hρ : IsDensity ρ)
    (hσ : IsDensity σ) :
    relEntropy (dephaseIn hσ.1.1.eigenvectorUnitary ρ) σ ≤ relEntropy ρ σ := by
  have hfix : dephaseIn hσ.1.1.eigenvectorUnitary σ = σ := dephaseIn_eigenbasis_eq_self hσ.1.1
  have h := data_processing_dephaseIn hσ.1.1.eigenvectorUnitary hρ hσ hfix
  rwa [hfix] at h

end QI

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
Full data processing inequality for the Umegaki relative entropy under CPTP maps.

The proof follows an integral representation of the relative entropy: for positive definite
`P`, `Q` of unit trace,

  `D(P‖Q) = ∫_0^∞ χ_t(P,Q) / (1+t)^2 dt`,

where `χ_t(P,Q) = ⟨Δ, 𝕄_t^{-1} Δ⟩` with `Δ = P - Q` and `𝕄_t` the (positive definite)
superoperator `X ↦ t • P X + X Q`.  Each `χ_t` is monotone under CPTP maps by a variational
argument together with the Kadison-Schwarz inequality for the (unital, completely positive)
adjoint channel, and the data processing inequality follows by integration.
-/
import RequestProject.QuantumRelativeEntropy

namespace QI

open Matrix MeasureTheory Filter Topology
open scoped ComplexOrder

universe u

variable {n m : Type u} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-! ### Traces of products of positive semidefinite matrices -/

omit [DecidableEq n] in
