/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## The finite-volume Ising model -/

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The real spin value `±1` attached to a Boolean spin variable. -/

lemma twoPoint_le_one (β : ℝ) (J : V → V → ℝ) (o : V) (d : V → ℕ) (n : ℕ) :
    twoPoint β J o d n ≤ 1 := by
  unfold twoPoint
  split
  · exact Finset.sup'_le _ _ fun v _ => corr_le_one β J o v
  · norm_num

end Ising

/-! ## The two abstract inputs of the Duminil-Copin–Tassion argument -/

/-- **Subcritical reduction.** A nonnegative, bounded quantity that contracts by a
factor `c < 1` over every scale step of length `L` decays exponentially. -/
