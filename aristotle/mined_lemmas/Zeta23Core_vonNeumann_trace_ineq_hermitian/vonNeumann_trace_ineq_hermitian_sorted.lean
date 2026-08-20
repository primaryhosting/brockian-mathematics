/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared absolute values of the entries of a unitary matrix is doubly
stochastic. -/

theorem vonNeumann_trace_ineq_hermitian_sorted {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ ea eb : Fin (Fintype.card n) ≃ n,
      Antitone (hA.eigenvalues ∘ ea) ∧ Antitone (hB.eigenvalues ∘ eb) ∧
        RCLike.re (Matrix.trace (A * B))
          ≤ ∑ i, hA.eigenvalues (ea i) * hB.eigenvalues (eb i) := by
  obtain ⟨ea, hea⟩ := exists_antitone_reindex hA.eigenvalues
  obtain ⟨eb, heb⟩ := exists_antitone_reindex hB.eigenvalues
  exact ⟨ea, eb, hea, heb,
    vonNeumann_trace_ineq_hermitian hA hB _ _ ea eb (fun _ => rfl) (fun _ => rfl) hea heb⟩

end Zeta23Core

