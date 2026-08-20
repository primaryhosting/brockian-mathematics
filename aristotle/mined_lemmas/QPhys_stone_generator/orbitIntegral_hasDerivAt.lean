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

lemma orbitIntegral_hasDerivAt (x : H) (u : ℝ) :
    HasDerivAt (fun v : ℝ => ∫ s in (0:ℝ)..v, U s x) (U u x) u :=
  intervalIntegral.integral_hasDerivAt_right (orbit_intervalIntegrable U hUcont x 0 u)
    ((hUcont x).stronglyMeasurableAtFilter _ _) (hUcont x).continuousAt

include hUadd hUcont in
