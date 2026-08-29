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

lemma gibbs_pointwise_strict {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p → 0 < q)
    (hne : p ≠ q) : p - q < p * Real.log (p / q) := by
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · have hq0 : 0 < q := lt_of_le_of_ne hq (by simpa [← hp0, eq_comm] using hne)
    simp [← hp0, hq0]
  · have hq0 : 0 < q := hpq hp0
    have hx : q / p ≠ 1 := by
      intro hx
      rw [div_eq_one_iff_eq (ne_of_gt hp0)] at hx
      exact hne hx.symm
    have hlog : Real.log (q / p) < q / p - 1 :=
      Real.log_lt_sub_one_of_pos (div_pos hq0 hp0) hx
    have hrw : Real.log (q / p) = -Real.log (p / q) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [hrw] at hlog
    have h := mul_lt_mul_of_pos_left hlog hp0
    have hpq' : p * (q / p - 1) = q - p := by field_simp
    rw [hpq'] at h
    linarith

/-- If the actual next-state distribution differs from the product of the two parts'
next-state distributions, the effective information across that bipartition is positive. -/
