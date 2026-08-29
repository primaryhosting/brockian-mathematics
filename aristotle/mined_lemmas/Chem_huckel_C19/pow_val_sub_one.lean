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

lemma pow_val_sub_one {w : ℂ} (hw : w ^ 19 = 1) (i : Fin 19) :
    w ^ ((i - 1 : Fin 19) : ℕ) * w = w ^ (i : ℕ) := by
  have h := pow_val_add_one hw (i - 1)
  rw [sub_add_cancel] at h
  exact h.symm

/-- The basic eigenvector computation: for any 19-th root of unity `w`, the geometric
vector `j ↦ w ^ j` is an eigenvector of the adjacency matrix of `C₁₉` with
eigenvalue `w + w⁻¹`. -/
