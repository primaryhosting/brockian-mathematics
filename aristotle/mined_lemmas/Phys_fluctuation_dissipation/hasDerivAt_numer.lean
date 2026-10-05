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
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not permit a
-- module docstring to precede the `import` line.)

import Mathlib

namespace Phys

open Finset

variable {ι : Type*} [Fintype ι]

/-- Boltzmann weight of state `i` for the Hamiltonian `E - f • A` at inverse
temperature `beta`, i.e. `exp (-beta * (E i - f * A i))`. -/

lemma hasDerivAt_numer (beta : ℝ) (E A : ι → ℝ) (g : ι → ℝ) (f : ℝ) :
    HasDerivAt (fun f => ∑ i, g i * weight beta E A f i)
      (beta * ∑ i, (A i * g i) * weight beta E A f i) f := by
  have h : HasDerivAt (fun f => ∑ i, g i * weight beta E A f i)
      (∑ i, g i * (beta * A i * weight beta E A f i)) f :=
    HasDerivAt.fun_sum (fun i _ => (hasDerivAt_weight beta E A f i).const_mul (g i))
  refine h.congr_deriv ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Fluctuation–dissipation theorem (static / classical linear response).**

For a classical system with energy levels `E` in the canonical ensemble at inverse
temperature `beta`, perturbed by a field `f` coupling to the observable `A`
(so the energy is `E i - f * A i`), the response of the equilibrium average of any
observable `B` to the field is `beta` times the equilibrium covariance of `A` and `B`:

  `d⟨B⟩/df = beta * (⟨A B⟩ - ⟨A⟩⟨B⟩)`.

Dissipation (the left-hand side, the susceptibility) is thus determined by the
equilibrium fluctuations (the right-hand side). -/
