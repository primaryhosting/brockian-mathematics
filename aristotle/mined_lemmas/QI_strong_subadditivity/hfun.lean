import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

open scoped BigOperators ComplexOrder
open Matrix

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Part I: Functional calculus for Hermitian matrices -/


noncomputable def hfun (f : ℝ → ℝ) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  if h : M.IsHermitian then
    (h.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => ((f (h.eigenvalues i) : ℝ) : ℂ)) *
      star (h.eigenvectorUnitary : Matrix n n ℂ)
  else 0

/-- `hfun` computed from an arbitrary spectral decomposition. -/
