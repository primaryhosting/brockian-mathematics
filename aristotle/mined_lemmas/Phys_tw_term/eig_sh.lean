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

lemma eig_sh (b : (Fin n × Fin n) → (Fin n × Fin n) → ℂ) (ψ : Conf n L → ℂ) (E0 : ℝ)
    (heig : ∀ c, ∑ c', Hchain b c c' * ψ c' = (E0 : ℂ) * ψ c) (c : Conf n L) :
    ∑ c', Hchain b c c' * ψ (sh c') = (E0 : ℂ) * ψ (sh c) := by
  have h : ∑ d, Hchain b (sh c) (sh d) * ψ (sh d) = ∑ c', Hchain b (sh c) c' * ψ c' :=
    Fintype.sum_bijective sh sh_bijective _ _ (fun d => rfl)
  have h2 : ∑ d, Hchain b c d * ψ (sh d) = ∑ d, Hchain b (sh c) (sh d) * ψ (sh d) :=
    Finset.sum_congr rfl fun d _ => by rw [Hchain_transl]
  rw [h2, h, heig (sh c)]

