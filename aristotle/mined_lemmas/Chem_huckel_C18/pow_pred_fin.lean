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

lemma pow_pred_fin (x : ℂ) (hx : x ^ 18 = 1) (i : Fin 18) :
    x ^ (((i - 1 : Fin 18)) : ℕ) = x ^ (i : ℕ) * x ^ 17 := by
  have h : ((i - 1 : Fin 18) : ℕ) = ((i : ℕ) + 17) % 18 := by
    rw [Fin.sub_def]
    norm_num
    omega
  rw [h, pow_mod_eighteen x hx, pow_add]

/-- `ζ^(17k) + ζ^k = 2 cos (2πk/18)`. -/
