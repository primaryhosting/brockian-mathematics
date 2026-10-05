/-
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
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

namespace Phys

variable {ι : Type*} [Fintype ι]

/-- Boltzmann weight of the microstate `i` for the perturbed Hamiltonian
`E i - f * B i` at inverse temperature `beta`. -/

lemma hasDerivAt_Zpart (beta : ℝ) (E B : ι → ℝ) :
    HasDerivAt (fun f => Zpart beta E B f)
      (∑ i, beta * B i * weight beta E B 0 i) 0 := by
  simpa [Zpart, Finset.sum_apply] using
    HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hasDerivAt_weight beta E B i)

/-- **Fluctuation–dissipation theorem** (classical, static form).

For a finite classical system in canonical equilibrium at inverse temperature `beta`
with energies `E`, the linear response of the observable `A` to a perturbation
`E i ↦ E i - f * B i` of the Hamiltonian equals `beta` times the equilibrium
covariance (the fluctuation) of `A` and `B`:

`d/df ⟨A⟩_f |_{f=0} = beta * (⟨A B⟩ - ⟨A⟩ ⟨B⟩)`. -/
