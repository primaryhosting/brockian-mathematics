import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to precede any module documentation, so the requested
header comment appears immediately after the single `import Mathlib` line.)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₉`, i.e. the Hückel matrix of the
carbon skeleton of a 19-membered annulene (with `α = 0`, `β = 1`). -/

lemma pow_val_add_one {w : ℂ} (hw : w ^ 19 = 1) (i : Fin 19) :
    w ^ ((i + 1 : Fin 19) : ℕ) = w ^ (i : ℕ) * w := by
  have h : ((i + 1 : Fin 19) : ℕ) = ((i : ℕ) + 1) % 19 := by
    simp [Fin.val_add]
  rw [h, ← pow_mod_nineteen hw, pow_succ]

