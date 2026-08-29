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

namespace Frontier

/-! ## Systems

A (discrete, finite) system consists of a finite set `ι` of elements, each of which can be
in one of finitely many states `Q`; a global state of the system is a function `ι → Q`.
The dynamics are given by a transition probability matrix (TPM): for every current global
state `s`, a probability distribution `prob s` over next global states. -/

/-- A transition probability matrix on the global state space `ι → Q`. -/
structure TPM (ι Q : Type) [Fintype ι] [DecidableEq ι] [Fintype Q] where
  /-- `prob s u` is the probability that the system moves from state `s` to state `u`. -/
  prob : (ι → Q) → (ι → Q) → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ s u, 0 ≤ prob s u
  /-- For each current state, the next-state probabilities sum to one. -/
  normalized : ∀ s, ∑ u, prob s u = 1

variable {ι Q : Type} [Fintype ι] [DecidableEq ι] [Fintype Q]

/-- The elements on one side of the bipartition determined by `S`. -/
abbrev Part (S : Finset ι) : Type := {i : ι // i ∈ S}

/-- The elements on the other side of the bipartition determined by `S`. -/
abbrev CoPart (S : Finset ι) : Type := {i : ι // i ∉ S}

/-- Restriction of a global state to the `S`-part of the system. -/

noncomputable def uniformPairSystem : TPM (Fin 2) Bool where
  prob _ _ := 1 / 4
  nonneg := by intro s u; norm_num
  normalized := by
    intro s
    simp [Finset.sum_const, Finset.card_univ]

example : Phi uniformPairSystem = 0 := by
  refine iit_phi_partition uniformPairSystem {0} ⟨0, by simp⟩ ?_
    ⟨fun _ _ => 1 / 2, fun _ _ => 1 / 2, by intro s u; norm_num [uniformPairSystem]⟩
  intro h
  have h1 : (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) := by rw [h]; exact Finset.mem_univ 1
  simp at h1

end Frontier

