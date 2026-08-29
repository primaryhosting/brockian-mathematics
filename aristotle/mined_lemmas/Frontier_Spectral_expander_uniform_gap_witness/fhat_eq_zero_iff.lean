import Mathlib
/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) : Type := Fin k → ZMod 2

/-- The basis vector flipping coordinate `i`. -/

lemma fhat_eq_zero_iff {k : ℕ} (f : Cube k → ℝ) (h : ∀ s, fhat f s = 0) : f = 0 := by
  funext x
  have hinv := fourier_inversion f x
  rw [Finset.sum_congr rfl (fun s _ => by rw [h s]; ring : ∀ s ∈ Finset.univ,
    fhat f s * chi s x = (0 : ℝ))] at hinv
  rw [Finset.sum_const_zero] at hinv
  have hpow : (2 : ℝ) ^ k ≠ 0 := by positivity
  have : f x = 0 := by
    rcases mul_eq_zero.mp hinv.symm with h1 | h1
    · exact absurd h1 hpow
    · exact h1
  simpa using this

/-- The characters are eigenvectors of the Laplacian, with eigenvalue twice the Hamming weight. -/
