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

lemma Zpart_pos [Nonempty ι] (beta : ℝ) (E B : ι → ℝ) (f : ℝ) : 0 < Zpart beta E B f :=
  Finset.sum_pos (fun i _ => weight_pos beta E B f i) Finset.univ_nonempty

omit [Fintype ι] in
