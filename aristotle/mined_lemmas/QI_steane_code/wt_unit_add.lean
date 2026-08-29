/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not permit a module
-- docstring before the `import` commands.)

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Setup

The state space of `7` qubits is modelled as the space of complex-valued functions on
`Vec := Fin 7 → ZMod 2`, the set of the `2^7` computational basis labels, with the
standard hermitian inner product `ip`.  Linear operators are `Matrix Vec Vec ℂ` acting
by `Matrix.mulVec`.
-/

/-- Computational basis labels for 7 qubits. -/
abbrev Vec := Fin 7 → ZMod 2

/-- The `𝔽₂`-bilinear form on `Vec`. -/

lemma wt_unit_add (i j : Fin 7) (s t : ZMod 2) : wt (unit i s + unit j t) ≤ 2 := by
  have hsub : (Finset.univ.filter (fun k => (unit i s + unit j t) k ≠ 0))
      ⊆ ({i, j} : Finset (Fin 7)) := by
    intro k hk
    simp only [Finset.mem_filter, Pi.add_apply, unit] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hcon
    push_neg at hcon
    rw [if_neg hcon.1, if_neg hcon.2] at hk
    simp at hk
  have h2 : ({i, j} : Finset (Fin 7)).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  exact (Finset.card_le_card hsub).trans h2

/-! ## The Knill-Laflamme condition on the code space -/

