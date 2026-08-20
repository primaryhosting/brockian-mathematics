import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

open MeasureTheory

/-! ## Basic objects -/

/-- Physical space `ℝ^d`, with its Euclidean structure and Lebesgue measure. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Negative part `t⁻ = max (-t) 0` of a real number. -/

def AntisymmetricWave {N : ℕ} (psi : Config N → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin N)) (x : Config N),
    psi (permConfig σ x) = (Equiv.Perm.sign σ : ℤ) * psi x

/-- **Stability of matter** with constant `C`: for every number `N` of electrons and `K` of
nuclei with charges bounded by `1`, and every normalized antisymmetric wave function, the
energy is bounded below by `-C (N + K)`.  The crucial point is that the bound is *linear*
in the number of particles. -/
