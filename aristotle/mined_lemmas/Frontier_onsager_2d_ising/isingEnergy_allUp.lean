import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

/-! ## The 2D square-lattice Ising model on an `L × L` torus -/

/-- The real spin value `±1` attached to a Boolean spin variable. -/

lemma isingEnergy_allUp (L : ℕ) [NeZero L] :
    isingEnergy L (fun _ => true) = -(2 * (L * L)) := by
  have hcard : Fintype.card (ZMod L × ZMod L) = L * L := by simp [ZMod.card]
  simp only [isingEnergy, spinVal, if_pos, mul_one, Finset.sum_const,
    Finset.card_univ, hcard, nsmul_eq_mul]
  push_cast
  ring

/-- The partition function is strictly positive at every inverse temperature. -/
