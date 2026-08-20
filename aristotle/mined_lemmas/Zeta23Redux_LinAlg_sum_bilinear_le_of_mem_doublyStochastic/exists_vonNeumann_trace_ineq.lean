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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

/-- Birkhoff + rearrangement: for antitone `mu`, `nu` and a doubly stochastic matrix `S`,
the bilinear form `∑ i j, S i j * (mu i * nu j)` is at most `∑ i, mu i * nu i`. -/

theorem exists_vonNeumann_trace_ineq {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ mu nu : Fin d → ℝ,
      (∃ eA : Equiv.Perm (Fin d), mu = hA.eigenvalues ∘ eA) ∧
      (∃ eB : Equiv.Perm (Fin d), nu = hB.eigenvalues ∘ eB) ∧
      Antitone mu ∧ Antitone nu ∧ (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  obtain ⟨eA, hEA⟩ := exists_antitone_eigenvalues_perm hA
  obtain ⟨eB, hEB⟩ := exists_antitone_eigenvalues_perm hB
  exact ⟨hA.eigenvalues ∘ eA, hB.eigenvalues ∘ eB, ⟨eA, rfl⟩, ⟨eB, rfl⟩, hEA, hEB,
    vonNeumann_trace_ineq hA hB rfl rfl hEA hEB⟩

end Zeta23Redux.LinAlg

