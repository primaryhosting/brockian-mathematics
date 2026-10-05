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

lemma EI_pos_of_ne (T : TPM ι Q) (S : Finset ι) (s : ι → Q)
    (a₀ : Part S → Q) (b₀ : CoPart S → Q)
    (hne : joint T S s a₀ b₀ ≠ margA T S s a₀ * margB T S s b₀) : 0 < EI T S := by
  have hcard : (0 : ℝ) < (Fintype.card (ι → Q) : ℝ) := by
    have h0 : 0 < Fintype.card (ι → Q) := Fintype.card_pos_iff.mpr ⟨s⟩
    exact_mod_cast h0
  refine div_pos (Finset.sum_pos' (fun t _ => ei_nonneg T S t)
    ⟨s, Finset.mem_univ s, ei_pos_of_ne T S s a₀ b₀ hne⟩) hcard

/-- **Integrated information is positive for a genuinely integrated system.** If across every
nontrivial bipartition the system's dynamics fail to factorize at some state, then `Φ > 0`. -/
