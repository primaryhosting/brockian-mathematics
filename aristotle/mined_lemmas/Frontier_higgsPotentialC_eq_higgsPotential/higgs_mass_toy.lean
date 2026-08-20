import Mathlib

/-!
# Higgs Mass Toy
Category: Frontier Physics
Target: Frontier.higgs_mass_toy
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The "Mexican hat" scalar potential of the abelian Higgs model, written as a
function of the modulus `r = |φ|` of the complex scalar field:
`V(r) = lam * (r² - v²)²`. -/

theorem higgs_mass_toy (g v lam A : ℝ) (hg : 0 < g) (hv : 0 < v) (hlam : 0 < lam) :
    -- the broken vacuum `r = v` is a global minimum of the potential, with zero energy
    (∀ r : ℝ, higgsPotential lam v v ≤ higgsPotential lam v r) ∧
      higgsPotential lam v v = 0 ∧
      -- the symmetric point is not a minimum: the symmetry is broken
      higgsPotential lam v v < higgsPotential lam v 0 ∧
      -- stationarity and positive curvature (physical Higgs mass squared)
      deriv (higgsPotential lam v) v = 0 ∧
      deriv (deriv (higgsPotential lam v)) v = 8 * lam * v ^ 2 ∧
      0 < deriv (deriv (higgsPotential lam v)) v ∧
      -- the gauge field acquires the mass term `m_A² A²` about the broken vacuum
      (∀ a : ℝ, gaugeQuadratic g v a = gaugeMassSq g v * a ^ 2) ∧
      0 < gaugeMassSq g v ∧
      Real.sqrt (gaugeMassSq g v) = g * v ∧
      0 < g * v ∧
      -- while about the symmetric point the gauge field remains massless
      (∀ a : ℝ, gaugeQuadratic g 0 a = 0) ∧
      -- complex-field formulation: the vacuum manifold is the circle `|φ| = v`,
      -- and the potential and kinetic term are `U(1)` invariant
      (∀ phi : ℂ, 0 ≤ higgsPotentialC lam v phi) ∧
      (∀ phi : ℂ, higgsPotentialC lam v phi = 0 ↔ ‖phi‖ = v) ∧
      (∀ (theta : ℝ) (phi : ℂ),
        higgsPotentialC lam v (Complex.exp (theta * Complex.I) * phi)
          = higgsPotentialC lam v phi) ∧
      (∀ (theta : ℝ) (dphi phi : ℂ),
        gaugeKinetic g A (Complex.exp (theta * Complex.I) * dphi)
            (Complex.exp (theta * Complex.I) * phi) = gaugeKinetic g A dphi phi) ∧
      -- the covariant kinetic term on the constant vacuum `φ = v` *is* the mass term
      gaugeKinetic g A 0 ((v : ℝ) : ℂ) = gaugeMassSq g v * A ^ 2 ∧
      -- and it vanishes identically at the symmetric point `φ = 0`
      gaugeKinetic g A 0 0 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    have : (0:ℝ) ≤ lam * (r ^ 2 - v ^ 2) ^ 2 :=
      mul_nonneg hlam.le (sq_nonneg _)
    simpa [higgsPotential] using this
  · simp [higgsPotential]
  · have h : (0:ℝ) < lam * v ^ 4 := by positivity
    simp only [higgsPotential]
    nlinarith [h]
  · rw [deriv_higgsPotential]; ring
  · rw [deriv2_higgsPotential]; ring
  · rw [deriv2_higgsPotential]
    have : (0:ℝ) < v ^ 2 := by positivity
    nlinarith
  · intro a; simp [gaugeQuadratic, gaugeMassSq]
  · have : (0:ℝ) < g ^ 2 * v ^ 2 := by positivity
    simpa [gaugeMassSq] using this
  · rw [gaugeMassSq, show g ^ 2 * v ^ 2 = (g * v) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  · positivity
  · intro a; simp [gaugeQuadratic]
  · intro phi
    have : (0:ℝ) ≤ lam * (‖phi‖ ^ 2 - v ^ 2) ^ 2 := mul_nonneg hlam.le (sq_nonneg _)
    simpa [higgsPotentialC] using this
  · intro phi
    rw [higgsPotentialC_eq_zero_iff lam v hlam phi]
    constructor
    · intro h; nlinarith [norm_nonneg phi]
    · intro h; rw [h]
  · intro theta phi; exact higgsPotentialC_gauge_invariant lam v theta phi
  · intro theta dphi phi; exact gaugeKinetic_gauge_invariant g A theta dphi phi
  · exact gaugeKinetic_vacuum g v A
  · exact gaugeKinetic_symmetric g A

end Frontier

