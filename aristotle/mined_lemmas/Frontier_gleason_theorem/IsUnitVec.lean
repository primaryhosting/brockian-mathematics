import Mathlib
/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Frontier

open Matrix

variable {n : ℕ}

/-! ## Basic notions -/

/-- The rank-one (orthogonal) projection onto the line spanned by a unit vector `v`,
written as the matrix `v vᴴ`. -/

def IsUnitVec (v : Fin n → ℂ) : Prop := star v ⬝ᵥ v = 1

/-- An orthogonal projection: a self-adjoint idempotent matrix.  These are exactly the
matrices of orthogonal projections onto closed subspaces, i.e. the quantum events. -/
