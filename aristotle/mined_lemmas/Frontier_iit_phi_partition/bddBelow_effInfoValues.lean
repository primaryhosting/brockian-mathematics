/-
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite *system*: a set of elements `V` together with nonnegative directed
interaction strengths `w u v` between them. -/
structure System (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Strength of the (directed) causal influence of `u` on `v`. -/
  w : V → V → ℝ
  /-- Interaction strengths are nonnegative. -/
  w_nonneg : ∀ u v, 0 ≤ w u v

/-- The *effective information* across the bipartition `(A, Aᶜ)` of a system:
the total interaction strength that is severed when the system is cut into the
two parts `A` and `Aᶜ`. -/

theorem bddBelow_effInfoValues (S : System V) : BddBelow (effInfoValues S) := by
  refine ⟨0, ?_⟩
  rintro x ⟨A, -, rfl⟩
  exact effInfo_nonneg S A

/-- Integrated information is nonnegative. -/
