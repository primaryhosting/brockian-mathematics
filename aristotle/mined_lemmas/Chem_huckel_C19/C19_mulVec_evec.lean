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

lemma C19_mulVec_evec (k : ℕ) :
    C19 *ᵥ evec k = ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ) • evec k := by
  have hw : (zeta19 ^ k) ^ 19 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, zeta19_pow_nineteen, one_pow]
  have h := C19_mulVec_geom hw
  rw [show (fun j : Fin 19 => (zeta19 ^ k) ^ (j : ℕ)) = evec k from rfl] at h
  rw [h, zeta19_pow_eq k, exp_add_inv_exp]

/-- The Vandermonde matrix whose `k`-th column is the `k`-th eigenvector. -/
