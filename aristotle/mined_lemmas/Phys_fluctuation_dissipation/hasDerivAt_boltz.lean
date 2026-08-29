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
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Boltzmann weight of state `i` for the Hamiltonian `E - f • A`, at inverse
temperature `β` and external field `f`. -/

lemma hasDerivAt_boltz (β : ℝ) (E A : ι → ℝ) (f₀ : ℝ) (i : ι) :
    HasDerivAt (fun f => boltz β E A f i) (β * A i * boltz β E A f₀ i) f₀ := by
  have h : HasDerivAt (fun f : ℝ => -β * (E i - f * A i)) (β * A i) f₀ := by
    simpa using (((hasDerivAt_id f₀).mul_const (A i)).const_sub (E i)).const_mul (-β)
  simpa [boltz, mul_comm, mul_assoc, mul_left_comm] using h.exp

omit [Nonempty ι] in
