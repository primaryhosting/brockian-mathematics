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

def RamseyProp (n k l : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), (∃ s, G.IsNClique k s) ∨ (∃ s, Gᶜ.IsNClique l s)

/-! ### The lower bound: a graph on 8 vertices with no triangle and no independent 4-set -/

/-- The circulant relation with connection set `{1, 4}` on `Fin 8`. -/
