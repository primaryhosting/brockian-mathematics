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

theorem eiAt_nonneg (sys : System V S) (A : Finset V) (x : V → S) : 0 ≤ eiAt sys A x := by
  simp only [eiAt]
  refine gibbs_sum_nonneg (fun y => sys.tpm x y)
    (fun y => margIn sys A x (resIn A y) * margOut sys A x (resOut A y))
    (fun y => sys.tpm_nonneg x y)
    (fun y => mul_nonneg (margIn_nonneg sys A x _) (margOut_nonneg sys A x _)) ?_
    (sys.tpm_sum x) ?_
  · intro y hy
    rcases mul_eq_zero.1 hy with hz | hz
    · exact le_antisymm (hz ▸ tpm_le_margIn sys A x y) (sys.tpm_nonneg x y)
    · exact le_antisymm (hz ▸ tpm_le_margOut sys A x y) (sys.tpm_nonneg x y)
  · rw [sum_split_mul A (margIn sys A x) (margOut sys A x), sum_margIn, sum_margOut, mul_one]

