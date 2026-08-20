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

lemma boundedBy_of_le {m : Type*} [Fintype m] [DecidableEq m] (v : m → Fin 1 → ℂ)
    (T : Finset m) (c : ℝ) (h : ∑ i ∈ T, ‖v i 0‖ ^ 2 ≤ c) :
    BoundedBy (∑ i ∈ T, outer (v i)) c := by
  rw [BoundedBy, sum_outer_eq_smul v T, ← sub_smul, ← Complex.ofReal_sub]
  exact Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.mpr h)

/-- **The base case of the Marcus–Spielman–Srivastava theorem**: `MSS` holds in dimension one,
where the statement amounts to splitting nonnegative reals summing to `1`, each at most `ε`,
into two groups of sum at most `1/2 + ε ≤ (1/√2 + √ε)²`. -/
