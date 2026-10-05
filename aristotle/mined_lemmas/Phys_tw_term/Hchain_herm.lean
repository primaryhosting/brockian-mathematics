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

lemma Hchain_herm (b : (Fin n × Fin n) → (Fin n × Fin n) → ℂ)
    (hb : ∀ p q, b q p = (starRingEnd ℂ) (b p q)) (c c' : Conf n L) :
    Hchain b c' c = (starRingEnd ℂ) (Hchain b c c') := by
  rw [Hchain, Hchain, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : ∀ i, i ≠ j → i ≠ j + 1 → c i = c' i
  · rw [if_pos (fun i hi hi' => (h i hi hi').symm), if_pos h, hb]
  · have h' : ¬ ∀ i, i ≠ j → i ≠ j + 1 → c' i = c i :=
      fun hc => h (fun i hi hi' => (hc i hi hi').symm)
    rw [if_neg h', if_neg h, map_zero]

