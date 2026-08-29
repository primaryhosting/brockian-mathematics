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
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

/-- Shannon entropy (in nats) of a finite probability vector `p`. -/

theorem landauer_general
    (k T Q ΔS_env S_init S_final : ℝ) (hT : 0 < T)
    (hClausius : ΔS_env = Q / T)
    (hSecondLaw : 0 ≤ k * (S_final - S_init) + ΔS_env) :
    k * T * (S_init - S_final) ≤ Q := by
  rw [hClausius] at hSecondLaw
  have h : k * (S_init - S_final) ≤ Q / T := by nlinarith [hSecondLaw]
  calc k * T * (S_init - S_final) = (k * (S_init - S_final)) * T := by ring
    _ ≤ (Q / T) * T := by nlinarith [h, hT.le]
    _ = Q := by field_simp

/--
**Landauer's principle.**

Erasing one bit dissipates at least `k T log 2` of heat.  Formally: a process takes the
system from the fair-bit distribution `(1/2, 1/2)` to the deterministic distribution
`(1, 0)`, so the system's thermodynamic entropy changes by
`k * (S_final - S_init)`; the heat `Q` released into a reservoir at temperature `T > 0`
changes the reservoir entropy by `Q / T` (Clausius) and the total entropy change is
nonnegative (second law).  Then `k * T * log 2 ≤ Q`.
-/
