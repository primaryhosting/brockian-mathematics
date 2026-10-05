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

lemma exists_antitone_reindex (f : Fin d → ℝ) : ∃ p : Equiv.Perm (Fin d), Antitone (f ∘ p) := by
  refine ⟨Tuple.sort fun i => -f i, ?_⟩
  have h := Tuple.monotone_sort fun i => -f i
  intro i j hij
  have hij' := h hij
  simp only [Function.comp_apply] at hij' ⊢
  linarith

end Zeta23Redux.LinAlg

