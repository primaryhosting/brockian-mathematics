/-
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index of inertia of a Hermitian matrix: the number of (strictly) positive
eigenvalues.  (For non-Hermitian matrices the value is set to `0`.) -/

theorem posIndex_eq (Q : Matrix n n 𝕜) (hQ : Q.IsHermitian) :
    posIndex Q = (Finset.univ.filter (fun i => 0 < hQ.eigenvalues i)).card := by
  rw [posIndex, dif_pos hQ]

/-- For a Hermitian matrix `G` there is an orthogonal projection `E` onto the range of `G`:
it is Hermitian, idempotent, acts as the identity on the range of `G`, kills everything
orthogonal to that range, and has trace equal to the rank of `G`. -/
