import Mathlib
/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- Two antitone functions monovary. -/

lemma sum_mul_comp_perm_le {mu nu : Fin d → ℝ} (hmu : Antitone mu) (hnu : Antitone nu)
    (τ : Equiv.Perm (Fin d)) : ∑ i, mu i * nu (τ i) ≤ ∑ i, mu i * nu i := by
  have := (monovary_of_antitone hmu hnu).sum_smul_comp_perm_le_sum_smul (σ := τ)
  simpa [smul_eq_mul] using this

/-- If `mu`, `nu` are antitone reorderings of `a`, `b`, then any permuted pairing of `a` with `b`
is dominated by the sorted pairing. -/
