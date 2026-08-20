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

theorem exists_antitone_eigenvalues_perm {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) : ∃ e : Equiv.Perm (Fin d), Antitone (hA.eigenvalues ∘ e) := by
  classical
  set q : Fin (Fintype.card (Fin d)) ≃ Fin d := Fintype.equivOfCardEq (Fintype.card_fin _) with hq
  refine ⟨(finCongr (Fintype.card_fin d).symm).trans q, ?_⟩
  have hmono : Monotone (finCongr (Fintype.card_fin d).symm) := by
    intro a b hab; simpa using hab
  have hcomp : (hA.eigenvalues ∘ ((finCongr (Fintype.card_fin d).symm).trans q))
      = hA.eigenvalues₀ ∘ (finCongr (Fintype.card_fin d).symm) := by
    funext i
    simp [Matrix.IsHermitian.eigenvalues, hq]
  rw [hcomp]
  exact hA.eigenvalues₀_antitone.comp_monotone hmono

/-- **Von Neumann's trace inequality** for Hermitian matrices.
If `mu` and `nu` list the eigenvalues of the Hermitian matrices `A` and `B` respectively
(each in some order, given by permutations `eA`, `eB`), and both lists are in decreasing
(antitone) order, then `Re (trace (A * B)) ≤ ∑ i, mu i * nu i`. -/
