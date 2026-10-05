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
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- reproduced verbatim as a module docstring immediately after the import.)

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

/-- Boltzmann weight of the microstate `i` at inverse temperature `β` for the perturbed
Hamiltonian `H_lam = E - lam • B`. -/

lemma hasDerivAt_resp (k tau t : ℝ) :
    HasDerivAt (resp k tau) ((1 / (k * tau)) * Real.exp (-t / tau)) t := by
  have h : HasDerivAt (fun s : ℝ => -s / tau) (-1 / tau) t := by
    simpa [neg_div] using ((hasDerivAt_id t).neg).div_const tau
  have := ((h.exp).const_sub 1).const_mul (1 / k)
  refine this.congr_deriv ?_
  field_simp

/-- **Dynamical fluctuation–dissipation theorem** for the Ornstein–Uhlenbeck model:
the response function `resp'` is `-beta` times the time derivative of the equilibrium
correlation function `corr`. -/
