/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain comment and is repeated as a docstring below.)

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ## Phases and signs -/

/-- Computational basis labels for `n` qubits: bit strings of length `n`. -/
abbrev Bits (n : ℕ) : Type := Fin n → ZMod 2

/-- The fourth root of unity `i ^ s` attached to `s : ZMod 4`. -/

lemma tp_mul {n : ℕ} (M N : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) :
    tp M * tp N = tp (fun q => M q * N q) := by
  ext a c
  simp only [tp, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  exact (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (ZMod 2)))
    (fun q j => M q (a q) j * N q j (c q))).symm

