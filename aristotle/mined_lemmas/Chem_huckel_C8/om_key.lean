/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is a plain block comment; its text is otherwise verbatim.)

import Mathlib

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₈`, indexed by `Fin 8` with cyclic
successor/predecessor. -/

lemma om_key (i k : Fin 8) :
    om ^ ((((i + 1 : Fin 8)) : ℕ) * (k : ℕ)) + om ^ ((((i - 1 : Fin 8)) : ℕ) * (k : ℕ))
      = om ^ ((i : ℕ) * (k : ℕ)) * (C8eig k : ℂ) := by
  have h1 : (((i + 1 : Fin 8)) : ℕ) = ((i : ℕ) + 1) % 8 := by fin_cases i <;> rfl
  have h2 : (((i - 1 : Fin 8)) : ℕ) = ((i : ℕ) + 7) % 8 := by fin_cases i <;> rfl
  have e1 : om ^ ((((i + 1 : Fin 8)) : ℕ) * (k : ℕ))
      = om ^ ((i : ℕ) * (k : ℕ)) * om ^ (k : ℕ) := by
    rw [← pow_add, h1]
    exact om_pow_congr (by simp [add_mul])
  have e2 : om ^ ((((i - 1 : Fin 8)) : ℕ) * (k : ℕ))
      = om ^ ((i : ℕ) * (k : ℕ)) * om ^ (7 * (k : ℕ)) := by
    rw [← pow_add, h2]
    exact om_pow_congr (by simp [add_mul])
  rw [e1, e2, ← mul_add, om_pow_add_inv (k : ℕ)]
  simp [C8eig]

