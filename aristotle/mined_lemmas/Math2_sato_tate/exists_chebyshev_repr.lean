import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

namespace Math2

open Filter Topology Set Polynomial

/-- The Sato–Tate density `(2/π) sin²θ` on the interval `[0, π]`. -/

lemma exists_chebyshev_repr (q : ℝ[X]) :
    ∃ (n : ℕ) (c : ℕ → ℝ), ∀ x : ℝ,
      q.eval x = ∑ m ∈ Finset.range n, c m * (Chebyshev.U ℝ m).eval x := by
  obtain ⟨c, hc⟩ := cheb_span_aux q.natDegree q le_rfl
  exact ⟨q.natDegree + 1, c, hc⟩

/-- Weierstrass approximation: continuous functions on `[0, π]` are uniformly approximated by
finite linear combinations of the Weyl test functions. -/
