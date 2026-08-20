import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/

noncomputable def nrm {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, (v i) ^ 2)

/-- A matrix is a contraction when it does not increase the Euclidean norm. -/
