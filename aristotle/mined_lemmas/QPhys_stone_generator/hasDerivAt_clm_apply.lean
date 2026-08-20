/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean does not allow a module docstring before the `import` line, so the header above is a
plain block comment; the same header is repeated as a module docstring below.)
-/
import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Stone's theorem: the infinitesimal generator of a strongly continuous one-parameter
unitary group on a complex Hilbert space is self-adjoint (as an unbounded, i.e. partially
defined, operator).
-/

namespace QPhys

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain of the infinitesimal generator of a one-parameter group `U`:
the set of vectors `x` for which the orbit map `t ↦ U t x` is differentiable at `0`. -/

lemma hasDerivAt_clm_apply (L : H →L[ℂ] H) {f : ℝ → H} {v : H} {s : ℝ}
    (h : HasDerivAt f v s) : HasDerivAt (fun t : ℝ => L (f t)) (L v) s :=
  (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h

section Group

variable [CompleteSpace H] (U : ℝ → H →L[ℂ] H)
  (hU0 : ∀ x, U 0 x = x)
  (hUadd : ∀ s t x, U (s + t) x = U s (U t x))
  (hUnorm : ∀ t x, ‖U t x‖ = ‖x‖)
  (hUcont : ∀ x, Continuous fun t : ℝ => U t x)

omit [CompleteSpace H] in
include hUnorm in
/-- Each `U t` preserves the inner product. -/
