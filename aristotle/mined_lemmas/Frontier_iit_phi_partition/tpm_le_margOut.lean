import Mathlib
/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

/-! ## A finite-sum Gibbs inequality

The nonnegativity of a Kullback–Leibler divergence between two finitely supported
probability distributions. -/

/-- One term of Gibbs' inequality: `p - q ≤ p * log (p / q)`, under the absolute
continuity assumption `q = 0 → p = 0`. -/

theorem tpm_le_margOut (sys : System V S) (A : Finset V) (x y : V → S) :
    sys.tpm x y ≤ margOut sys A x (resOut A y) := by
  have := Finset.single_le_sum (f := fun y' : V → S =>
      if resOut A y' = resOut A y then sys.tpm x y' else 0)
    (fun y' _ => by dsimp only; split_ifs <;> [exact sys.tpm_nonneg _ _; exact le_rfl])
    (Finset.mem_univ y)
  simpa [margOut] using this

