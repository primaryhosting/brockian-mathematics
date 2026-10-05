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

lemma submatrix_mem_doublyStochastic (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S ∈ doublyStochastic ℝ (Fin d)) (e f : Equiv.Perm (Fin d)) :
    S.submatrix e f ∈ doublyStochastic ℝ (Fin d) := by
  rw [mem_doublyStochastic_iff_sum] at hS ⊢
  obtain ⟨h0, hr, hc⟩ := hS
  refine ⟨fun i j => h0 _ _, fun i => ?_, fun j => ?_⟩
  · rw [show (∑ j, S.submatrix e f i j) = ∑ j, S (e i) (f j) from rfl, Equiv.sum_comp f (S (e i))]
    exact hr _
  · rw [show (∑ i, S.submatrix e f i j) = ∑ i, S (e i) (f j) from rfl,
      Equiv.sum_comp e (fun i => S i (f j))]
    exact hc _

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/
