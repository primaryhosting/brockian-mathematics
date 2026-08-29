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

lemma Hchain_transl (b : (Fin n × Fin n) → (Fin n × Fin n) → ℂ) (c c' : Conf n L) :
    Hchain b (sh c) (sh c') = Hchain b c c' := by
  have hstep : ∀ j : ZMod L,
      (if (∀ i, i ≠ j → i ≠ j + 1 → (sh c) i = (sh c') i)
        then b ((sh c) j, (sh c) (j + 1)) ((sh c') j, (sh c') (j + 1)) else 0)
      = (if (∀ i, i ≠ j + 1 → i ≠ j + 1 + 1 → c i = c' i)
        then b (c (j + 1), c (j + 1 + 1)) (c' (j + 1), c' (j + 1 + 1)) else 0) := by
    intro j
    by_cases hcond : ∀ i, i ≠ j + 1 → i ≠ j + 1 + 1 → c i = c' i
    · have hpos : ∀ i, i ≠ j → i ≠ j + 1 → (sh c) i = (sh c') i := by
        intro i hi hi'
        exact hcond (i + 1) (fun hx => hi (add_right_cancel hx))
          (fun hx => hi' (add_right_cancel hx))
      rw [if_pos hpos, if_pos hcond]
      rfl
    · have hneg : ¬ ∀ i, i ≠ j → i ≠ j + 1 → (sh c) i = (sh c') i := by
        intro hc2
        refine hcond fun i hi hi' => ?_
        have h1 : i - 1 ≠ j := fun hx => hi (by rw [← hx]; ring)
        have h2 : i - 1 ≠ j + 1 := fun hx => hi' (by rw [← hx]; ring)
        have := hc2 (i - 1) h1 h2
        simpa [sh, sub_add_cancel] using this
      rw [if_neg hneg, if_neg hcond]
  calc Hchain b (sh c) (sh c') = ∑ j : ZMod L,
      (if (∀ i, i ≠ j + 1 → i ≠ j + 1 + 1 → c i = c' i)
        then b (c (j + 1), c (j + 1 + 1)) (c' (j + 1), c' (j + 1 + 1)) else 0) :=
        Finset.sum_congr rfl fun j _ => hstep j
    _ = Hchain b c c' :=
        Fintype.sum_bijective (fun j : ZMod L => j + 1) (Equiv.addRight (1 : ZMod L)).bijective
          _ _ (fun j => rfl)

