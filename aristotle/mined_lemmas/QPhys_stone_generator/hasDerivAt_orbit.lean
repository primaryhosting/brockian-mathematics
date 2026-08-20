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

lemma hasDerivAt_orbit {x : H} (hx : x ∈ generatorDomain U) (s : ℝ) :
    HasDerivAt (fun t : ℝ => U t x) (U s (orbitDeriv U x)) s := by
  have h1 : HasDerivAt (fun t : ℝ => U (t - s) x) (orbitDeriv U x) s := by
    have hg : HasDerivAt (fun u : ℝ => U u x) (orbitDeriv U x) (s - s) := by
      simpa using hasDerivAt_orbit_zero U hx
    exact HasDerivAt.comp_sub_const s s hg
  have h2 : HasDerivAt (fun t : ℝ => U s (U (t - s) x)) (U s (orbitDeriv U x)) s :=
    hasDerivAt_clm_apply (U s) h1
  have h : (fun t : ℝ => U s (U (t - s) x)) = fun t : ℝ => U t x := by
    funext t
    rw [← hUadd]
    ring_nf
  rwa [h] at h2

omit [CompleteSpace H] in
include hU0 hUnorm in
/-- The generator is symmetric. -/
