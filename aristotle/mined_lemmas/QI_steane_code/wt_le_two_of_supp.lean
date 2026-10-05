/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the
-- header above is a plain block comment; it is repeated verbatim as the module
-- docstring immediately after the import.)

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## The classical ingredients: the `[7,4,3]` Hamming code and its dual -/

/-- A binary register of 7 bits.  Also used to index the computational basis of the
7-qubit Hilbert space. -/
abbrev Reg := Fin 7 → ZMod 2

/-- The `𝔽₂`-bilinear form used both for parity checks and for Pauli phases. -/

lemma wt_le_two_of_supp {a : Reg} {p q : Fin 7} (h : ∀ k, k ≠ p → k ≠ q → a k = 0) :
    wt a ≤ 2 := by
  have hsub : (Finset.univ.filter (fun i => a i ≠ 0)) ⊆ ({p, q} : Finset (Fin 7)) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    by_cases hp : k = p
    · simp [hp]
    · by_cases hq : k = q
      · simp [hq]
      · exact absurd (h k hp hq) hk
  calc wt a ≤ ({p, q} : Finset (Fin 7)).card := Finset.card_le_card hsub
    _ ≤ 2 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        simp

/-! ## The 7-qubit Hilbert space, Pauli errors and the Steane code space -/

/-- Pauli operators.  `pauliLM a b` is (up to an irrelevant global phase) the
Pauli operator `X^a Z^b`: it flips the bits selected by `a` and applies the sign
`(-1)^{b·v}`.  With `a = b = eᵢ` one gets `Yᵢ` up to phase, so for a fixed qubit
`q` the four operators `pauliLM a b` with `a, b` supported in `{q}` span all
operators acting on that qubit. -/
