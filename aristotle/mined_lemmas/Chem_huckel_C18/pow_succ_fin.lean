import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean 4 requires `import` commands to occur at the very beginning of a file,
before any module docstring, hence the header comment above appears just after the import.
-/

open Complex Polynomial Matrix

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma pow_succ_fin (x : ℂ) (hx : x ^ 18 = 1) (i : Fin 18) :
    x ^ (((i + 1 : Fin 18)) : ℕ) = x ^ (i : ℕ) * x := by
  have h : ((i + 1 : Fin 18) : ℕ) = ((i : ℕ) + 1) % 18 := by simp [Fin.val_add]
  rw [h, pow_mod_eighteen x hx, pow_succ]

/-- Shifting the index by `-1` multiplies the power by `x ^ 17`. -/
