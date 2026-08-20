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

lemma orbitIntegral_translate (x : H) (t e : ℝ) :
    U t (∫ s in (0:ℝ)..e, U s x)
      = (∫ s in (0:ℝ)..(t + e), U s x) - ∫ s in (0:ℝ)..t, U s x := by
  have h2 : U t (∫ s in (0:ℝ)..e, U s x) = ∫ s in (0:ℝ)..e, U t (U s x) :=
    (ContinuousLinearMap.intervalIntegral_comp_comm (U t)
      (orbit_intervalIntegrable U hUcont x 0 e)).symm
  have h3 : (∫ s in (0:ℝ)..e, U t (U s x)) = ∫ s in (0:ℝ)..e, U (t + s) x := by
    refine intervalIntegral.integral_congr ?_
    intro s _
    exact (hUadd t s x).symm
  have h4 : (∫ s in (0:ℝ)..e, U (t + s) x) = ∫ s in (t + 0)..(t + e), U s x :=
    intervalIntegral.integral_comp_add_left (fun s => U s x) t
  rw [h2, h3, h4, add_zero]
  exact (intervalIntegral.integral_interval_sub_left
    (orbit_intervalIntegrable U hUcont x 0 (t + e)) (orbit_intervalIntegrable U hUcont x 0 t)).symm

include hU0 hUadd hUcont in
/-- Averages of the orbit over an interval lie in the domain of the generator. -/
