/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {d : ℕ}

/-- The rearrangement step: for antitone `mu`, `nu` and a permutation `σ`,
`∑ i, mu i * nu (σ i) ≤ ∑ i, mu i * nu i`. -/

lemma exists_antitone_perm (f : Fin d → ℝ) : ∃ e : Equiv.Perm (Fin d), Antitone (f ∘ e) := by
  refine ⟨Tuple.sort (fun i => -f i), ?_⟩
  have h := Tuple.monotone_sort (fun i => -f i)
  intro i j hij
  have hij' := h hij
  simp only [Function.comp_apply] at hij' ⊢
  linarith

/-- The hypotheses of `vonNeumann_trace_ineq` are satisfiable: every Hermitian matrix admits
a decreasing enumeration of its eigenvalues. -/
