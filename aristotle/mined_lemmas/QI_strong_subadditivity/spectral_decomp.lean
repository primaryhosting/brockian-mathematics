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


theorem spectral_decomp {M : Matrix n n ℂ} (h : M.IsHermitian) :
    M = (h.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => ((h.eigenvalues i : ℝ) : ℂ)) *
      star (h.eigenvectorUnitary : Matrix n n ℂ) := by
  simpa [Unitary.conjStarAlgAut, Function.comp_def] using h.spectral_theorem

/-- Functional calculus for Hermitian matrices: `hfun f M` applies the real function `f`
to the eigenvalues of `M` (junk value `0` if `M` is not Hermitian). -/
