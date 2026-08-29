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

lemma oneQubit_entry (i : Fin 7) (m : ZMod 2 → ZMod 2 → ℂ) (x y : Vec) :
    (if (∀ k, k ≠ i → x k = y k) then m (x i) (y i) else 0)
      = ∑ s : ZMod 2, ∑ t : ZMod 2, ccOf m s t * pauli (unit i s) (unit i t) x y := by
  have hp : ∀ s t : ZMod 2, pauli (unit i s) (unit i t) x y
      = if x = y + unit i s then chi (t * y i) else 0 := by
    intro s t
    unfold pauli
    rw [dotp_unit]
  by_cases hagree : ∀ k, k ≠ i → x k = y k
  · rw [if_pos hagree]
    have hcond : ∀ s : ZMod 2, (x = y + unit i s) ↔ (s = x i + y i) := by
      intro s
      rw [eq_add_unit_iff]
      constructor
      · rintro ⟨-, h2⟩
        rw [h2]
        generalize y i = q
        generalize s = r
        revert q r
        decide
      · rintro rfl
        refine ⟨hagree, ?_⟩
        generalize x i = p
        generalize y i = q
        revert p q
        decide
    simp only [hp, hcond]
    rw [sum_zmod2 (fun s => ∑ t : ZMod 2, ccOf m s t * (if s = x i + y i then chi (t * y i) else 0))]
    simp only [sum_zmod2]
    rcases zmod2_cases (x i) with hx | hx <;> rcases zmod2_cases (y i) with hy | hy <;>
      rw [hx, hy] <;> simp +decide [ccOf, chi] <;> try ring
  · rw [if_neg hagree]
    have : ∀ s t : ZMod 2, pauli (unit i s) (unit i t) x y = 0 := by
      intro s t
      rw [hp]
      rw [if_neg]
      intro h
      exact hagree ((eq_add_unit_iff i s x y).mp h).1
    simp [this]

