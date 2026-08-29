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
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Phys

/-! ## Part I: an abstract twist (flux insertion) estimate

We model a quantum system on a finite configuration space `α`: states are functions
`ψ : α → ℂ`, the (squared) norm is `∑ c, ‖ψ c‖^2`, and a Hamiltonian is a matrix
`H : α → α → ℂ`.  `qf H ψ` is the energy expectation `⟪ψ, H ψ⟫` (real part).
-/

section Abstract

variable {α : Type*} [Fintype α]

/-- The energy expectation value `⟪ψ, H ψ⟫` (real part). -/

lemma lsm_hypotheses_satisfiable (c0 : Conf n L) (hc0 : M2 c0 = 0) :
    ∃ (b : (Fin n × Fin n) → (Fin n × Fin n) → ℂ) (B : ℝ) (ψ : Conf n L → ℂ) (E0 : ℝ),
      (∀ p q, b q p = (starRingEnd ℂ) (b p q)) ∧
      (∀ p q, b p q ≠ 0 → w n p.1 + w n p.2 = w n q.1 + w n q.2) ∧
      (∀ p, ∑ q, ‖b p q‖ ≤ B) ∧ nrm2 ψ = 1 ∧ (∀ c, ψ c ≠ 0 → M2 c = 0) ∧
      (∀ c, ∑ c', Hchain b c c' * ψ c' = (E0 : ℂ) * ψ c) ∧
      (∀ φ : Conf n L → ℂ, nrm2 φ = 1 → E0 ≤ qf (Hchain b) φ) := by
  have hH : ∀ c c' : Conf n L, Hchain (fun _ _ => (0 : ℂ)) c c' = 0 := by
    intro c c'; simp [Hchain]
  refine ⟨fun _ _ => 0, 0, fun c => if c = c0 then 1 else 0, 0, by simp, by simp, by simp, ?_, ?_,
    by simp [hH], ?_⟩
  · simp [nrm2, apply_ite norm, Finset.sum_ite_eq']
  · intro c hc
    by_cases h : c = c0
    · rw [h]; exact hc0
    · simp [h] at hc
  · intro φ _
    simp [qf, hH]

/-- The zero magnetization sector of the spin-1/2 chain with two sites is nonempty. -/
example : M2 (L := 2) (fun j => if j = 0 then (0 : Fin 2) else 1) = 0 := by decide

end Chain

end Phys

