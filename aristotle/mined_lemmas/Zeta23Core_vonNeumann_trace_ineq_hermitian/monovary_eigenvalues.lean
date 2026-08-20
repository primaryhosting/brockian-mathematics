import Mathlib

/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Core

open Matrix Finset

/-! ### A rearrangement bound for doubly stochastic matrices -/

/-- If `a` and `b` monovary, then the bilinear form `∑ j k, D j k * (a j * b k)` attached to a
doubly stochastic matrix `D` is at most `∑ i, a i * b i`.  This is the combinatorial heart of the
von Neumann trace inequality: it follows from Birkhoff's theorem together with the rearrangement
inequality. -/

lemma monovary_eigenvalues {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Monovary hA.eigenvalues hB.eigenvalues := by
  set e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _) with he
  intro i j hij
  have hAi : hA.eigenvalues i = hA.eigenvalues₀ (e.symm i) := rfl
  have hAj : hA.eigenvalues j = hA.eigenvalues₀ (e.symm j) := rfl
  have hBi : hB.eigenvalues i = hB.eigenvalues₀ (e.symm i) := rfl
  have hBj : hB.eigenvalues j = hB.eigenvalues₀ (e.symm j) := rfl
  rw [hAi, hAj]
  rcases le_or_gt (e.symm j) (e.symm i) with h | h
  · exact hA.eigenvalues₀_antitone h
  · rw [hBi, hBj] at hij
    exact absurd (hB.eigenvalues₀_antitone h.le) (not_le.2 hij)

/-! ### The von Neumann trace inequality -/

/-- **Von Neumann trace inequality**, Hermitian case.  For Hermitian matrices `A`, `B` over an
`RCLike` field, the real part of `tr (A * B)` is at most the sum of the products of the
eigenvalues of `A` and of `B`, each listed in decreasing order (`Matrix.IsHermitian.eigenvalues₀`
is antitone by `Matrix.IsHermitian.eigenvalues₀_antitone`). -/
