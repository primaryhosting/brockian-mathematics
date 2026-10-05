import Mathlib

/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open SimpleGraph Finset

/-- `RamseyProp n k l` says that every simple graph on `n` vertices contains either a clique
of size `k` or an independent set (a clique of its complement) of size `l`. -/

theorem wagner_compl_cliqueFree_four : wagnerᶜ.CliqueFree 4 := by
  intro t; revert t; decide

/-! ### The upper bound -/

section Upper

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Ramsey `R(3,3) ≤ 6`, in the form needed below: in a triangle-free graph, any set of at
least `6` vertices contains an independent set of size `3`. -/
