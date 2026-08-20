/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The proof follows the classical route: writing `A = U Dα U*`, `B = V Dβ V*` via the spectral
theorem, one gets `tr (A B) = ∑ j k, α j * β k * |W j k|²` for the unitary `W = U* V`.
The matrix of squared moduli of a unitary matrix is doubly stochastic, so by Birkhoff's theorem
(`exists_eq_sum_perm_of_mem_doublyStochastic`) the right-hand side is a convex combination of the
quantities `∑ j, α j * β (σ j)`, each of which is bounded by `∑ i, a i * b i` by the rearrangement
inequality (`Monovary.sum_mul_comp_perm_le_sum_mul`).
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

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared absolute values of the entries of a matrix. -/

theorem exists_sorted_eigenvalues_trace_le {m : ℕ} {A B : Matrix (Fin m) (Fin m) 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ a b : Fin m → ℝ, Antitone a ∧ Antitone b ∧
      (∃ sa : Equiv.Perm (Fin m), a = hA.eigenvalues ∘ sa) ∧
      (∃ sb : Equiv.Perm (Fin m), b = hB.eigenvalues ∘ sb) ∧
      RCLike.re (trace (A * B)) ≤ ∑ i, a i * b i := by
  obtain ⟨sa, ha⟩ := exists_antitone_perm hA.eigenvalues
  obtain ⟨sb, hb⟩ := exists_antitone_perm hB.eigenvalues
  exact ⟨_, _, ha, hb, ⟨sa, rfl⟩, ⟨sb, rfl⟩,
    vonNeumann_trace_ineq_hermitian hA hB ha hb rfl rfl⟩

end Zeta23Core

