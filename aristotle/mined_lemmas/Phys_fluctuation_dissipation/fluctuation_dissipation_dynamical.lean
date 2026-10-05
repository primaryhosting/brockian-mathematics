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

theorem fluctuation_dissipation_dynamical (beta k tau t : ℝ) (hbeta : beta ≠ 0) :
    HasDerivAt (resp k tau) (-beta * deriv (corr beta k tau) t) t := by
  have hc : deriv (corr beta k tau) t = -(1 / (beta * k * tau)) * Real.exp (-t / tau) :=
    (hasDerivAt_corr beta k tau t).deriv
  rw [hc]
  refine (hasDerivAt_resp k tau t).congr_deriv ?_
  rcases eq_or_ne k 0 with hk | hk
  · simp [hk]
  · rcases eq_or_ne tau 0 with ht | ht
    · simp [ht]
    · field_simp

end Phys

