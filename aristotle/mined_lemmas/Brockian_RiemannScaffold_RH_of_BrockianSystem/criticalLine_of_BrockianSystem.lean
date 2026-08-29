import Mathlib
import Brockian.RiemannScaffold

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
#print axioms Brockian.RiemannScaffold.RH_of_BrockianSystem
#print axioms Brockian.RiemannScaffold.nonempty_brockianSystem_iff_RH

/-
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace Brockian
namespace RiemannScaffold

/-! ## The Brockian system and the critical-line theorem -/

/-- A *nontrivial zero* of the Riemann zeta function: a zero lying in the open critical
strip `0 < Re s < 1`. -/

theorem criticalLine_of_BrockianSystem {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (B : BrockianSystem H) (s : ℂ) (hs : 0 < s.re)
    (hz : riemannZeta s = 0) : s.re = 1 / 2 := by
  by_cases h1 : s.re < 1
  · exact RH_of_BrockianSystem B s ⟨hz, hs, h1⟩
  · exact absurd hz (riemannZeta_ne_zero_of_one_le_re (not_lt.mp h1))

/-! ## Non-vacuity: a canonical space carrying a Brockian system exactly under RH

To show that the hypothesis of `RH_of_BrockianSystem` is not vacuous (and to pin down
exactly how strong it is), we build a canonical inner product space — the algebraic span of
the standard orthonormal family in `ℓ²` indexed by the nontrivial zeros — and show that it
carries a Brockian system if and only if the Riemann Hypothesis holds. -/

/-- The index set: the nontrivial zeros of `ζ`. -/
abbrev ZeroIdx : Type := {s : ℂ // IsNontrivialZero s}

instance : DecidableEq ZeroIdx := Classical.decEq _

/-- The standard unit vector of `ℓ²(ZeroIdx, ℂ)` attached to a nontrivial zero. -/
