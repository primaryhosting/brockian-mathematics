/-
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the required
-- header appears above as a plain block comment and is repeated as a module docstring below.)

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

namespace Phys

variable {ι : Type*} [Fintype ι]

/-- Unnormalized Boltzmann weight of the microstate `i` for the canonical ensemble at inverse
temperature `β`, with unperturbed energy `E i` and the observable `A` coupled to an external
field `f` (perturbed energy `E i - f * A i`). -/

lemma hasDerivAt_boltzmann (beta : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) :
    HasDerivAt (fun f => boltzmann beta E A f i) (beta * A i * boltzmann beta E A f i) f := by
  have h : HasDerivAt (fun f : ℝ => beta * (f * A i - E i)) (beta * A i) f := by
    simpa using (((hasDerivAt_id f).mul_const (A i)).sub_const (E i)).const_mul beta
  simpa [boltzmann, mul_comm, mul_left_comm, mul_assoc] using h.exp

