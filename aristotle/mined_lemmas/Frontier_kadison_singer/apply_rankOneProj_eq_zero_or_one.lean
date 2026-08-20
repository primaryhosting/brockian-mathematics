/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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

open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace Frontier
namespace KadisonSinger

/-! ## The setting

Let `H` be a complex Hilbert space with a distinguished orthonormal (Hilbert) basis `e : ι → H`.
The *diagonal* subalgebra `𝒟` (an atomic MASA in `B(H)`, isomorphic to `ℓ^∞(ι)`) consists of the
bounded operators that are diagonalised by the basis.  The Kadison–Singer problem asks whether
every pure state of `𝒟` extends *uniquely* to a state of `B(H)`; this was answered
affirmatively by Marcus, Spielman and Srivastava.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The rank-one orthogonal projection onto the line spanned by a unit vector `u`, i.e. `u u*`. -/

lemma apply_rankOneProj_eq_zero_or_one {ι : Type*} {e : HilbertBasis ι ℂ H}
    {psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ} (hpure : IsPureOnDiagonal e psi) (i : ι) :
    psi (rankOneProj (e i)) = 0 ∨ psi (rankOneProj (e i)) = 1 := by
  have hu : ‖e i‖ = 1 := e.orthonormal.1 i
  have hmem := rankOneProj_mem_diagonal e i
  have h := hpure _ hmem _ hmem
  rw [rankOneProj_mul_self (e i) hu] at h
  have : psi (rankOneProj (e i)) * (psi (rankOneProj (e i)) - 1) = 0 := by
    rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination h1)

omit [CompleteSpace H] in
/-- For a finite index set the atoms of the diagonal MASA sum to the identity. -/
