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

def BoundedBy {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (c : ℝ) : Prop :=
  Matrix.PosSemidef ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - M)

/-- **The Marcus–Spielman–Srivastava theorem** (Weaver's `KS_2`), in dimension `d`:
any resolution of the identity by vectors of squared length at most `ε` can be split into two
parts, each of spectral norm at most `(1/√2 + √ε)²`. -/
