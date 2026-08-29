/-
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset
open scoped Classical

namespace Phys

variable {X : Type*} [Fintype X]

/-- State visited by a path at (natural-number) time `n`, clamped to the horizon `N`. -/

lemma crooks_core (hDB : DetailedBalance β E p N) (γ : Fin (N + 1) → X) :
    Real.exp (-β * E 0 (st γ 0)) * ∏ t ∈ range N, p t (st γ t) (st γ (t + 1)) =
      Real.exp (β * Wfwd E N γ) * Real.exp (-β * E N (st γ N)) *
        ∏ t ∈ range N, p t (st γ (t + 1)) (st γ t) := by
  set A := ∏ t ∈ range N, p t (st γ t) (st γ (t + 1)) with hA
  set B := ∏ t ∈ range N, p t (st γ (t + 1)) (st γ t) with hB
  set S1 := ∑ t ∈ range N, E (t + 1) (st γ t) with hS1
  set S2 := ∑ t ∈ range N, E (t + 1) (st γ (t + 1)) with hS2
  set S0 := ∑ t ∈ range N, E t (st γ t) with hS0
  have hDBp : A * Real.exp (-β * S1) = B * Real.exp (-β * S2) :=
    prod_detailedBalance hDB γ
  have hAeq : A = B * Real.exp (-β * S2 + β * S1) := by
    have h : A * Real.exp (-β * S1) * Real.exp (β * S1) =
        B * Real.exp (-β * S2) * Real.exp (β * S1) := by rw [hDBp]
    rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add] at h
    simpa using h
  have htel : E 0 (st γ 0) + S2 = S0 + E N (st γ N) := by
    have h1 : (∑ i ∈ range (N + 1), E i (st γ i))
        = (∑ i ∈ range N, E (i + 1) (st γ (i + 1))) + E 0 (st γ 0) :=
      Finset.sum_range_succ' (fun i => E i (st γ i)) N
    have h2 : (∑ i ∈ range (N + 1), E i (st γ i))
        = (∑ i ∈ range N, E i (st γ i)) + E N (st γ N) :=
      Finset.sum_range_succ (fun i => E i (st γ i)) N
    rw [hS2, hS0]
    linarith
  have hW : Wfwd E N γ = S1 - S0 := by
    simp only [Wfwd, hS1, hS0, Finset.sum_sub_distrib]
  rw [hAeq, hW]
  rw [show Real.exp (-β * E 0 (st γ 0)) * (B * Real.exp (-β * S2 + β * S1)) =
      B * (Real.exp (-β * E 0 (st γ 0)) * Real.exp (-β * S2 + β * S1)) by ring,
    show Real.exp (β * (S1 - S0)) * Real.exp (-β * E N (st γ N)) * B =
      B * (Real.exp (β * (S1 - S0)) * Real.exp (-β * E N (st γ N))) by ring,
    ← Real.exp_add, ← Real.exp_add]
  congr 2
  linear_combination (-β) * htel

/-- Microscopic (trajectory-level) Crooks relation. -/
