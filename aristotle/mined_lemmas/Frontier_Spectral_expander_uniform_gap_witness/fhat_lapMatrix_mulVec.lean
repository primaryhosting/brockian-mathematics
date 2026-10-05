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

lemma fhat_lapMatrix_mulVec {k : ℕ} (v : Cube k → ℝ) (s : Cube k) :
    fhat ((hypercube k).lapMatrix ℝ *ᵥ v) s = (2 * wt s : ℝ) * fhat v s := by
  have h : ∀ x : Cube k, ((hypercube k).lapMatrix ℝ *ᵥ v) x * chi s x
      = (k : ℝ) * (v x * chi s x) - ∑ i, v (x + flip i) * chi s x := by
    intro x
    rw [hypercube_lapMatrix_mulVec, sub_mul, Finset.sum_mul]
    ring
  rw [fhat, Finset.sum_congr rfl (fun x _ => h x), Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_comm]
  have h2 : ∀ i : Fin k, ∑ x : Cube k, v (x + flip i) * chi s x = sgn (s i) * fhat v s := by
    intro i
    have : ∑ x : Cube k, v (x + flip i) * chi s x
        = ∑ y : Cube k, v y * chi s (y + flip i) :=
      Fintype.sum_equiv (Equiv.addRight (flip i)) _ _ (fun x => by
        simp only [Equiv.coe_addRight]
        rw [flip_add_flip])
    rw [this, fhat, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [chi_add_right]
    simp [chi, dot_flip_right]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h2 i), ← Finset.sum_mul, sum_sgn_eq, ← fhat]
  ring

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian of the hypercube graph
`Q_k` on `2 ^ k` vertices is exactly `2`.  In particular the family `(Q_k)` has a spectral gap
bounded below by `2`, uniformly in `k`. -/
