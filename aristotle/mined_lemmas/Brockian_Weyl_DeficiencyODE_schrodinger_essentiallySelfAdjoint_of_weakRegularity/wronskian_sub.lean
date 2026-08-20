import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
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

namespace Brockian.Weyl.DeficiencyODE

open scoped InnerProductSpace
open Filter Topology

/-!
## Unbounded operators: graphs, adjoints, essential self-adjointness
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The graph of the (generally unbounded) operator `T` defined on the domain `D ≤ E`,
viewed as a submodule of `E × E`. -/

lemma wronskian_sub (q : ℤ → ℝ) (z : ℂ) (c : ℤ → ℂ)
    (heq : ∀ n, (q n : ℂ) * c n - c (n + 1) - c (n - 1) = z * c n) (n : ℤ) :
    wronskian c (n - 1) - wronskian c n = z.im * ‖c n‖ ^ 2 := by
  have hA := congrArg Complex.re (heq n)
  have hB := congrArg Complex.im (heq n)
  simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im] at hA hB
  have hnorm : ‖c n‖ ^ 2 = (c n).re ^ 2 + (c n).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1 : n - 1 + 1 = n := by ring
  simp only [wronskian, Complex.mul_im, Complex.conj_re, Complex.conj_im, hnorm, h1]
  linear_combination (-(c n).im) * hA + (c n).re * hB

