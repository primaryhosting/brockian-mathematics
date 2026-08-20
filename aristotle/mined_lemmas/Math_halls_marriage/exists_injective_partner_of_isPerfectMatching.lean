import Mathlib

/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
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

set_option grind.warning false

namespace Math

open Function SimpleGraph

/-- From a perfect matching one extracts a partner function: an involution-free choice of
the unique `M`-neighbour of each vertex. -/

theorem exists_injective_partner_of_isPerfectMatching {V : Type*} {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    ∃ f : V → V, Function.Injective f ∧ ∀ v, G.Adj v (f v) := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hM
  choose f hf huniq using hM
  refine ⟨f, ?_, fun v => M.adj_sub (hf v)⟩
  intro v w hvw
  have hv : M.Adj (f v) v := (hf v).symm
  have hw : M.Adj (f v) w := hvw ▸ (hf w).symm
  have h1 := huniq (f v) v hv
  have h2 := huniq (f v) w hw
  exact h1.trans h2.symm

/-- A matching saturating a set `s` yields an injective map sending each vertex of `s` to an
adjacent vertex. -/
