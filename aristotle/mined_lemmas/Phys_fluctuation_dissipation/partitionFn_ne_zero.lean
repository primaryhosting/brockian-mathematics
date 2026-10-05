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

lemma partitionFn_ne_zero (β : ℝ) (H : ι → ℝ) : partitionFn β H ≠ 0 :=
  ne_of_gt (partitionFn_pos β H)

omit [Fintype ι] [Nonempty ι] in
/-- Derivative in the coupling `l` of the Boltzmann weight for the perturbed
Hamiltonian `H - l B`, evaluated at `l = 0`. -/
