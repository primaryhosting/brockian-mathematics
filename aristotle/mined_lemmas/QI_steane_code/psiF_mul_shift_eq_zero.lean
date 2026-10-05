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

lemma psiF_mul_shift_eq_zero (a : Reg) (i j : Bool) (ha : wt a ≤ 2)
    (h : a ≠ 0 ∨ i ≠ j) (v : Reg) : psiF i v * psiF j (v + a) = 0 := by
  unfold psiF
  by_cases h1 : v ∈ cosetOf i
  · by_cases h2 : v + a ∈ cosetOf j
    · exfalso
      rw [cosetOf, Finset.mem_image] at h1 h2
      obtain ⟨u, hu, hu'⟩ := h1
      obtain ⟨u', hu2, hu2'⟩ := h2
      -- in characteristic two, `a = (v + a) + v`
      have hav : a = (v + a) + v := by
        rw [add_comm v a, add_assoc, add_self_reg, add_zero]
      by_cases hij : i = j
      · subst hij
        have haa : a = u' + u := by
          rw [hav, ← hu2', ← hu', char2_cancel]
        have hd := dual_min_dist u' hu2 u hu (by rw [← haa]; exact ha)
        rw [← haa] at hd
        exact (h.resolve_right (fun hne => hne rfl)) hd
      · -- `i ≠ j`, so the two shifts differ by the all-ones vector
        have haa : a = u' + u + tv := by
          rw [hav, ← hu2', ← hu', char2_regroup, add_comm (shiftv j) (shiftv i),
            shiftv_add_shiftv hij]
        exact coset_min_wt u' hu2 u hu (by rw [← haa]; exact ha)
    · rw [if_neg h2, mul_zero]
  · rw [if_neg h1, zero_mul]

/-- The master inner-product computation. -/
