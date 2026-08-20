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


theorem hfun_spec (f : ℝ → ℝ) {M U : Matrix n n ℂ} {μ : n → ℝ}
    (hU : U ∈ unitaryGroup n ℂ)
    (hM : M = U * diagonal (fun i => ((μ i : ℝ) : ℂ)) * star U) :
    hfun f M = U * diagonal (fun i => ((f (μ i) : ℝ) : ℂ)) * star U := by
  have hHerm : M.IsHermitian := isHermitian_of_spectral hM
  rw [hfun, dif_pos hHerm]
  refine (conj_diag_congr f (hHerm.eigenvectorUnitary).2 hU ?_).symm
  rw [← spectral_decomp hHerm, hM]

/-- The matrix logarithm of a Hermitian matrix (with the convention `log 0 = 0`). -/
