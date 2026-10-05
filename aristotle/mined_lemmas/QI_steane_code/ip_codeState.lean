import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalise the statement that the seven–qubit Steane CSS code corrects an
arbitrary error on a single qubit, in the standard Knill–Laflamme form:

for any two single–qubit Pauli errors `E₁`, `E₂` there is a constant `c`
(depending only on the errors) such that
`⟪E₁ ψ, E₂ φ⟫ = c * ⟪ψ, φ⟫` for all code states `ψ, φ`.

Everything is set up concretely.  The `2^7`-dimensional state space is modelled
as the space of functions `V → ℂ` where `V = Fin 7 → ZMod 2` indexes the
computational basis.  Pauli operators `X^a Z^b` act by
`(X^a Z^b) |v⟩ = (-1)^{b·v} |v + a⟩`, i.e. by `pauliOp`.  The Steane code space
is spanned by the two logical basis states
`|0_L⟩ = Σ_{v ∈ C} |v⟩` and `|1_L⟩ = Σ_{v ∈ C^⊥ \ C} |v⟩`,
where `C` is the `[7,3]` simplex code (the row span of the Hamming parity check
matrix `Hm`) and `C^⊥` is the `[7,4]` Hamming code.  Concretely a codeword `v`
lies in `C^⊥` iff all three parity checks vanish (`InD v`), and it lies in `C`
iff moreover it has even weight (`par v = 0`).
-/

namespace QI

/-- Bit strings of length seven: the index set of the computational basis. -/
abbrev V := Fin 7 → ZMod 2

/-- The mod-2 inner product of two bit strings. -/

lemma ip_codeState (α β γ δ : ℂ) :
    ip (codeState α β) (codeState γ δ)
      = 8 * ((starRingEnd ℂ) α * γ + (starRingEnd ℂ) β * δ) := by
  have hsummand : ∀ v : V, (starRingEnd ℂ) (codeState α β v) * codeState γ δ v
      = (if (InD v ∧ par v = 0) then (starRingEnd ℂ) α * γ else 0)
        + (if (InD v ∧ par v = 1) then (starRingEnd ℂ) β * δ else 0) := by
    intro v
    by_cases hv : InD v
    · rcases zmod2_cases (par v) with hp | hp <;> simp [codeState, hv, hp]
    · simp [codeState, hv]
  rw [ip, Finset.sum_congr rfl (fun v _ => hsummand v), Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    card_simplex, card_simplex_coset]
  ring


end QI

#print axioms QI.steane_code
#print axioms QI.ip_codeState

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

