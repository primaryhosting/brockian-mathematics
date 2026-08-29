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

def effInfo (S : System V) (A : Finset V) : ℝ :=
  ∑ u ∈ A, ∑ v ∈ Aᶜ, (S.w u v + S.w v u)

/-- A bipartition is *proper* when both parts are nonempty. -/

def IsProper (A : Finset V) : Prop := A.Nonempty ∧ Aᶜ.Nonempty

/-- The set of effective-information values over all proper bipartitions. -/

def effInfoValues (S : System V) : Set ℝ :=
  (fun A => effInfo S A) '' {A : Finset V | IsProper A}

/-- Integrated information `Φ`: the minimum (infimum) of the effective information
over all proper bipartitions of the system.  (With the Mathlib convention
`sInf ∅ = 0`, a system with fewer than two elements has `Φ = 0`.) -/

noncomputable def phi (S : System V) : ℝ := sInf (effInfoValues S)

/-- A system is *disconnected* when it admits a proper bipartition across which
no interaction whatsoever takes place. -/

def Disconnected (S : System V) : Prop :=
  ∃ A : Finset V, IsProper A ∧ ∀ u ∈ A, ∀ v ∈ Aᶜ, S.w u v = 0 ∧ S.w v u = 0

/-- Effective information across any bipartition is nonnegative. -/

theorem effInfo_nonneg (S : System V) (A : Finset V) : 0 ≤ effInfo S A := by
  refine Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => ?_
  exact add_nonneg (S.w_nonneg u v) (S.w_nonneg v u)

theorem bddBelow_effInfoValues (S : System V) : BddBelow (effInfoValues S) := by
  refine ⟨0, ?_⟩
  rintro x ⟨A, -, rfl⟩
  exact effInfo_nonneg S A

/-- Integrated information is nonnegative. -/

theorem phi_nonneg (S : System V) : 0 ≤ phi S := by
  rcases Set.eq_empty_or_nonempty (effInfoValues S) with h | h
  · simp [phi, h, Real.sInf_empty]
  · refine le_csInf h ?_
    rintro x ⟨A, -, rfl⟩
    exact effInfo_nonneg S A

/-- **Integrated information vanishes for a disconnected system.**
If a system splits into two nonempty parts with no interaction between them,
then the effective information across that bipartition is `0`, and since `Φ` is
the minimum of a set of nonnegative quantities, `Φ = 0`. -/

theorem iit_phi_partition (S : System V) (h : Disconnected S) : phi S = 0 := by
  obtain ⟨A, hA, hcut⟩ := h
  have hzero : effInfo S A = 0 := by
    refine Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun v hv => ?_
    obtain ⟨h1, h2⟩ := hcut u hu v hv
    simp [h1, h2]
  refine le_antisymm ?_ (phi_nonneg S)
  have hmem : (0 : ℝ) ∈ effInfoValues S := ⟨A, hA, hzero⟩
  exact csInf_le (bddBelow_effInfoValues S) hmem

section Examples

/-- The two-element system with no interactions at all. -/
