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

lemma orbit_mem_domain {x : H} (hx : x ∈ generatorDomain U) (s : ℝ) :
    U s x ∈ generatorDomain U ∧ orbitDeriv U (U s x) = U s (orbitDeriv U x) := by
  have key : HasDerivAt (fun t : ℝ => U t (U s x)) (U s (orbitDeriv U x)) 0 := by
    have h : (fun t : ℝ => U t (U s x)) = fun t : ℝ => U s (U t x) := by
      funext t
      rw [← hUadd, ← hUadd, add_comm]
    rw [h]
    exact hasDerivAt_clm_apply (U s) (hasDerivAt_orbit_zero U hx)
  exact ⟨⟨_, key⟩, by simp [orbitDeriv, key.deriv]⟩

omit [CompleteSpace H] in
include hUadd in
/-- Differentiability of the orbit map at an arbitrary time. -/
