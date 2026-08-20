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

lemma deficiency_solution_eq_zero (q : ℤ → ℝ) (z : ℂ) (hz : z.im ≠ 0) (c : ℤ → ℂ)
    (hsum : Summable fun n => ‖c n‖ ^ 2)
    (heq : ∀ n, (q n : ℂ) * c n - c (n + 1) - c (n - 1) = z * c n) : ∀ n, c n = 0 := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · -- pass to the complex conjugate solution
    set c' : ℤ → ℂ := fun n => (starRingEnd ℂ) (c n) with hc'
    have hsum' : Summable fun n => ‖c' n‖ ^ 2 := by simpa [hc'] using hsum
    have heq' : ∀ n, (q n : ℂ) * c' n - c' (n + 1) - c' (n - 1) = ((starRingEnd ℂ) z) * c' n := by
      intro n
      have := congrArg (starRingEnd ℂ) (heq n)
      simpa [hc', map_sub, map_mul, Complex.conj_ofReal] using this
    have him : 0 < ((starRingEnd ℂ) z).im := by
      simpa [Complex.conj_im] using hneg
    intro n
    have := deficiency_solution_eq_zero_of_im_pos q _ him c' hsum' heq' n
    simpa [hc'] using congrArg (starRingEnd ℂ) this
  · exact deficiency_solution_eq_zero_of_im_pos q z hpos c hsum heq

/-!
## The discrete Schrödinger operator

We realise the one-dimensional Schrödinger operator `H = -Δ + V` on `ℓ²(ℤ)` (equivalently, on any
complex Hilbert space equipped with a Hilbert basis indexed by `ℤ`), defined on the dense domain
of finitely supported vectors, i.e. the algebraic span of the basis:
`H e n = 2 e n - e (n+1) - e (n-1) + V n • e n`.
The potential `V` is an arbitrary real-valued function; no regularity is assumed.
-/

/-- The action of the discrete Schrödinger operator `-Δ + V` on the `n`-th basis vector. -/
