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

import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Statement: The FDT relates linear response to equilibrium correlations.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- Boltzmann weight of the state `w` at inverse temperature `beta` for the
Hamiltonian `E - f • A`, i.e. the unperturbed energy `E` perturbed by an external
field `f` coupled to the observable `A`. -/

lemma hasDerivAt_partition (beta : ℝ) (E A : Ω → ℝ) (f : ℝ) :
    HasDerivAt (fun f => partition beta E A f)
      (∑ w, beta * A w * weight beta E A f w) f := by
  apply HasDerivAt.fun_sum
  intro w _
  exact hasDerivAt_weight beta E A f w

/-- **Fluctuation–dissipation theorem** (static, classical form).

For a finite classical system with energy `E` at inverse temperature `beta`,
perturbed by an external field `f` coupled to the observable `A`, the linear
response of any observable `B` — the derivative of its equilibrium expectation
value with respect to the field — equals `beta` times the equilibrium covariance
(the correlation of the fluctuations) of `A` and `B`:

`d⟨B⟩_f / df = beta * (⟨A·B⟩_f - ⟨A⟩_f ⟨B⟩_f)`. -/
