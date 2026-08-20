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

lemma hasDerivAt_orbit_zero {x : H} (hx : x ∈ generatorDomain U) :
    HasDerivAt (fun t : ℝ => U t x) (orbitDeriv U x) 0 := by
  obtain ⟨y, hy⟩ := hx
  simpa [orbitDeriv, hy.deriv] using hy

omit [CompleteSpace H] in
include hUadd in
/-- The domain is invariant under the group, and the generator commutes with it. -/
