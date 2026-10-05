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

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`
(there are `2 ^ k` of them). -/
abbrev Cube (k : ℕ) : Type := Fin k → ZMod 2


theorem fourier_inversion {k : ℕ} (v : Cube k → ℝ) (x : Cube k) :
    ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        (∑ y : Cube k, v y * chi S y) * chi S x = (2 ^ k : ℝ) * v x := by
  have step : ∀ S ∈ (Finset.univ : Finset (Fin k)).powerset,
      (∑ y : Cube k, v y * chi S y) * chi S x = ∑ y : Cube k, v y * chi S (y + x) := by
    intro S _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by rw [chi_add]; ring
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  have step2 : ∀ y : Cube k,
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset, v y * chi S (y + x)
        = if y = x then (2 ^ k : ℝ) * v y else 0 := by
    intro y
    rw [← Finset.mul_sum, sum_chi]
    rcases eq_or_ne y x with rfl | hne
    · rw [if_pos (cube_add_self y), if_pos rfl]; ring
    · rw [if_neg (fun h => hne ((cube_add_eq_zero_iff y x).mp h)), if_neg hne]; ring
  rw [Finset.sum_congr rfl fun y _ => step2 y]
  simp

/-- Every eigenvalue of the hypercube Laplacian is of the form `2 |S|`. -/
