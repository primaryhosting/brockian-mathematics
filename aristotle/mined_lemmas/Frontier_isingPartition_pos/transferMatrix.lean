import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

namespace Frontier

/-! ## The two-dimensional Ising model on a periodic square lattice -/

/-- The real spin value attached to a Boolean spin variable: `true ↦ +1`, `false ↦ -1`. -/

noncomputable def transferMatrix (n : ℕ) (K : ℝ) : Matrix (RowConfig n) (RowConfig n) ℝ :=
  Matrix.of fun s s' => Real.exp (K * (rowCoupling s s' + rowInternal s))

/-- Entries of a matrix power as a sum over paths: `(T ^ (m+1)) x y` is the sum,
over all choices `f` of `m` intermediate states, of the product of the transition
weights along the path `x, f 0, …, f (m-1), y`. -/
