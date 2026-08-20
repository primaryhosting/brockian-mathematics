import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- A bilinear form against a doubly stochastic matrix is bounded by the "sorted" pairing,
when both weight vectors are listed in the same (decreasing) order.

This is the Birkhoff + rearrangement step of von Neumann's trace inequality. -/

theorem exists_vonNeumann_trace_ineq {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ mu nu : Fin d → ℝ, (∃ σ : Equiv.Perm (Fin d), mu = hA.eigenvalues ∘ σ) ∧
      (∃ τ : Equiv.Perm (Fin d), nu = hB.eigenvalues ∘ τ) ∧ Antitone mu ∧ Antitone nu ∧
      (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  obtain ⟨σ, hσ⟩ := exists_antitone_perm hA.eigenvalues
  obtain ⟨τ, hτ⟩ := exists_antitone_perm hB.eigenvalues
  exact ⟨hA.eigenvalues ∘ σ, hB.eigenvalues ∘ τ, ⟨σ, rfl⟩, ⟨τ, rfl⟩, hσ, hτ,
    vonNeumann_trace_ineq hA hB ⟨σ, rfl⟩ ⟨τ, rfl⟩ hσ hτ⟩

end Zeta23Redux.LinAlg

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

