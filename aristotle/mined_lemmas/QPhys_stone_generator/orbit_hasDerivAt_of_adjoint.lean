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

lemma orbit_hasDerivAt_of_adjoint {y : H} (hy : y ∈ (generator U).adjoint.domain) :
    HasDerivAt (fun t : ℝ => U t y) (-(Complex.I • (generator U).adjoint ⟨y, hy⟩)) 0 := by
  set z : H := (generator U).adjoint ⟨y, hy⟩ with hzdef
  have hcontz : Continuous fun s : ℝ => Complex.I • U (-s) z :=
    (((hUcont z).comp continuous_neg)).const_smul Complex.I
  have hFTC : HasDerivAt (fun tau : ℝ => ∫ s in (0:ℝ)..tau, Complex.I • U (-s) z)
      (Complex.I • U (-(0:ℝ)) z) 0 :=
    intervalIntegral.integral_hasDerivAt_right (hcontz.intervalIntegrable _ _)
      (hcontz.stronglyMeasurableAtFilter _ _) hcontz.continuousAt
  have hfun : (fun tau : ℝ => U (-tau) y - y)
      = fun tau : ℝ => ∫ s in (0:ℝ)..tau, Complex.I • U (-s) z := by
    funext tau
    exact adjoint_orbit_eq U hU0 hUadd hUnorm hUcont hy tau
  have h1 : HasDerivAt (fun tau : ℝ => U (-tau) y - y) (Complex.I • z) 0 := by
    rw [hfun]
    simpa [hU0] using hFTC
  have h2 : HasDerivAt (fun tau : ℝ => U (-tau) y) (Complex.I • z) 0 := by
    simpa using h1.add_const y
  have h2' : HasDerivAt (fun tau : ℝ => U (-tau) y) (Complex.I • z) (-(0:ℝ)) := by
    simpa using h2
  have h3 := h2'.scomp (𝕜 := ℝ) 0 (hasDerivAt_neg (0:ℝ))
  have h4 : ((fun tau : ℝ => U (-tau) y) ∘ (Neg.neg : ℝ → ℝ)) = fun t : ℝ => U t y := by
    funext t
    simp
  rw [h4] at h3
  simpa using h3

include hU0 hUadd hUnorm hUcont in
/-- The adjoint of the generator is contained in the generator. -/
