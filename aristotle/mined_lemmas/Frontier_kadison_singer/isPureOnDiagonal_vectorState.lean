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

lemma isPureOnDiagonal_vectorState {ι : Type*} (e : HilbertBasis ι ℂ H) (i : ι) :
    IsPureOnDiagonal e (vectorState (e i)) := by
  intro A hA B hB
  obtain ⟨cA, hcA⟩ := hA i
  obtain ⟨cB, hcB⟩ := hB i
  have hu : ⟪e i, e i⟫_ℂ = 1 := by
    have : ‖e i‖ = 1 := e.orthonormal.1 i
    simp [inner_self_eq_norm_sq_to_K, this]
  simp only [vectorState_apply, ContinuousLinearMap.mul_apply, hcB, hcA, map_smul,
    inner_smul_right, hu]
  ring

omit [CompleteSpace H] in
/-- If the restriction of a state to the diagonal MASA is pure, its value on each atom
`P_i = e_i e_i^*` is either `0` or `1`. -/
