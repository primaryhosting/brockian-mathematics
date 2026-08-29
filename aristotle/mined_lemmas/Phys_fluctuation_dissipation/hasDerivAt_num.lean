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

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Boltzmann weight `e^{-β H(i)}` of the microstate `i`. -/

lemma hasDerivAt_num (β : ℝ) (H B A : ι → ℝ) :
    HasDerivAt (fun l : ℝ => ∑ i, A i * gibbsWeight β (fun j => H j - l * B j) i)
      (∑ i, A i * (β * B i * gibbsWeight β H i)) 0 :=
  HasDerivAt.fun_sum (fun i _ => ((hasDerivAt_gibbsWeight β H B i).const_mul (A i)))

/--
**Fluctuation–dissipation theorem** (static / classical Kubo form).

For a finite classical system in canonical equilibrium at inverse temperature `β`
with Hamiltonian `H`, perturbing the Hamiltonian by `-l·B` and measuring the
observable `A`, the linear response coefficient (the static susceptibility,
i.e. the derivative of the equilibrium average of `A` with respect to the
coupling `l` at `l = 0`) equals `β` times the equilibrium correlation
(covariance) of `A` and `B`:

`χ_{AB} = β (⟨A B⟩ - ⟨A⟩⟨B⟩)`.

Dissipation (the response to an external field) is thus determined by the
spontaneous equilibrium fluctuations.
-/
