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
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

variable {ι : Type*} [Fintype ι]

/-- The Boltzmann weight `exp (-β (E i - λ A i))` of the microstate `i`, for the
Hamiltonian `E` perturbed by the field `λ` coupled to the observable `A`. -/

lemma hasDerivAt_boltzmannWeight (beta : ℝ) (E A : ι → ℝ) (i : ι) (lam : ℝ) :
    HasDerivAt (fun l => boltzmannWeight beta E A l i)
      (beta * A i * boltzmannWeight beta E A lam i) lam := by
  have h : HasDerivAt (fun l : ℝ => -beta * (E i - l * A i)) (beta * A i) lam := by
    have h0 : HasDerivAt (fun l : ℝ => -beta * (E i - l * A i))
        (-beta * -(1 * A i)) lam :=
      (((hasDerivAt_id lam).mul_const (A i)).const_sub (E i)).const_mul (-beta)
    simpa using h0
  simpa [boltzmannWeight, mul_comm] using h.exp

/-- **Static fluctuation–dissipation theorem (Kubo).**

For a finite classical system with energies `E`, in equilibrium at inverse
temperature `β`, perturb the Hamiltonian by `-λ A`.  Then the linear response
(susceptibility) of the observable `A` to the field `λ`, i.e. the derivative at
`λ = 0` of the equilibrium expectation `⟨A⟩_λ`, equals `β` times the equilibrium
fluctuation `⟨A²⟩ - ⟨A⟩²` of `A` in the unperturbed system.

The analytic content is the quotient rule `HasDerivAt.div` applied to
`⟨A⟩_λ = (∑ i, A i * w i λ) / (∑ i, w i λ)`. -/
