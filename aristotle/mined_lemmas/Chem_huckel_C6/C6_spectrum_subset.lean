import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix

/-- The adjacency matrix (over `ℝ`) of the cycle graph `C₆`, i.e. the Hückel matrix of
benzene in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`. -/

lemma C6_spectrum_subset {mu : ℝ} {v : Fin 6 → ℝ} (hv : v ≠ 0) (h : C6adj *ᵥ v = mu • v) :
    mu = 2 ∨ mu = 1 ∨ mu = -1 ∨ mu = -2 := by
  have hp := C6_eigenvalue_root hv h
  have hfac : (mu - 2) * (mu - 1) * (mu + 1) * (mu + 2) = 0 := by linarith [hp, sq_nonneg mu]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))

