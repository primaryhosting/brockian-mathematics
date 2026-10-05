import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
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

namespace Phys

/-! ## Shannon entropy -/

/-- Shannon entropy (in nats) of a finitely supported weight function. -/

lemma entropy_two_point_le (u v eps : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (h : 1 - eps ≤ u) :
    -(u * Real.log u + v * Real.log v) ≤ eps + 2 * Real.sqrt eps := by
  have hv_le : v ≤ eps := by linarith
  have hv1 : v ≤ 1 := by linarith
  have h1 : -(u * Real.log u) ≤ v := by
    have hu' : u = 1 - v := by linarith
    rw [hu']
    exact neg_mul_log_one_sub_le v hv hv1
  have h2 : -(v * Real.log v) ≤ 2 * Real.sqrt v := neg_mul_log_le_two_sqrt v hv
  have h3 : Real.sqrt v ≤ Real.sqrt eps := Real.sqrt_le_sqrt hv_le
  linarith

/-! ## Landauer's principle -/

/-- **Landauer's principle.**

A one-bit memory, initially in the uniform (maximally uncertain) state `(1/2, 1/2)`,
is coupled to a heat bath whose energy levels are `E` and which starts in thermal
equilibrium (the Gibbs state) at temperature `T`.  The joint memory–bath system then
evolves by an arbitrary invertible (Liouville / measure-preserving) dynamics `U`.

If the process *erases* the bit up to an error `eps`, i.e. it leaves the memory in the
definite state `m₀` with probability at least `1 - eps`, then the heat dissipated into
the bath satisfies

  `Q ≥ k T (log 2 - eps - 2 √eps)`.

In the limit of perfect erasure (`eps → 0`) this is exactly the Landauer bound
`Q ≥ k T log 2`.  (An error term is unavoidable: `Phys.finalMem_uniform_lt_one` shows
that perfect erasure is impossible for an invertible dynamics on a finite phase
space with a strictly positive bath state.) -/
