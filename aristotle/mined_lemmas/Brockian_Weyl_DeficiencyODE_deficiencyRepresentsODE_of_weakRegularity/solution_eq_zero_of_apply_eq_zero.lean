import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Set MeasureTheory

namespace Brockian.Weyl.DeficiencyODE

/-- The state space of a first-order linear system of `n` equations. -/
abbrev State (n : ℕ) : Type := Fin n → ℂ

variable {n : ℕ}

/-- *Weak regularity* of the coefficient family of the first-order linear system
`u' t = A t (u t)`: the coefficient operators depend continuously on time.  This is the
hypothesis retained in the Weyl-theoretic statement below. -/

theorem solution_eq_zero_of_apply_eq_zero {A : ℝ → (State n →L[ℂ] State n)}
    (hA : WeakRegularity A) {u : ℝ → State n} (hu : ∀ t, HasDerivAt u (A t (u t)) t)
    {t₀ : ℝ} (h0 : u t₀ = 0) : u = 0 := by
  funext t
  obtain ⟨a, b, ht, ht₀⟩ : ∃ a b, t ∈ Ioo a b ∧ t₀ ∈ Ioo a b :=
    ⟨min t t₀ - 1, max t t₀ + 1, ⟨by
        have := min_le_left t t₀; linarith, by have := le_max_left t t₀; linarith⟩,
      ⟨by have := min_le_right t t₀; linarith, by have := le_max_right t t₀; linarith⟩⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hA.continuousOn
  set K : NNReal := ⟨max C 0, le_max_right _ _⟩ with hK
  have hvK : ∀ s ∈ Ioo a b, LipschitzOnWith K (fun x : State n => A s x) univ := by
    intro s hs
    have hle : ‖A s‖₊ ≤ K := by
      have h1 : ‖A s‖ ≤ C := hC s (Ioo_subset_Icc_self hs)
      simpa [hK, ← NNReal.coe_le_coe] using le_trans h1 (le_max_left C 0)
    exact ((A s).lipschitz.weaken hle).lipschitzOnWith
  have hzero : ∀ s : ℝ, HasDerivAt (fun _ : ℝ => (0 : State n)) (A s ((0 : ℝ → State n) s)) s := by
    intro s
    simpa using (hasDerivAt_const s (0 : State n))
  have heq : EqOn u (fun _ : ℝ => (0 : State n)) (Ioo a b) := by
    refine ODE_solution_unique_of_mem_Ioo (v := fun s x => A s x) (s := fun _ => univ)
      hvK ht₀ (fun s _ => ⟨hu s, mem_univ _⟩) (fun s _ => ⟨hzero s, mem_univ _⟩) ?_
    simpa using h0
  simpa using heq ht

/-- The deficiency space is faithfully represented by the initial data of the ODE: the
evaluation map is injective. -/
