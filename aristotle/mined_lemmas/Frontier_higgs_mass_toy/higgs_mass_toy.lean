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

/-- The Mexican-hat potential of the abelian Higgs toy model, written as a function of the
modulus `r = |φ|` of the complex scalar field:  `V(r) = lam * (r ^ 2 - v ^ 2) ^ 2`. -/

theorem higgs_mass_toy {g lam v : ℝ} (hg : 0 < g) (hlam : 0 < lam) (hv : 0 < v) :
    (∀ r : ℝ, 0 ≤ r → higgsPotential lam v v ≤ higgsPotential lam v r) ∧
      (∀ r : ℝ, 0 ≤ r → higgsPotential lam v r ≤ higgsPotential lam v v → r = v) ∧
      0 < gaugeMass g v ∧ gaugeMass g 0 = 0 := by
  obtain ⟨hmin, hnonneg, huniq, _hzero⟩ := higgs_vev_is_unique_minimum hlam hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [hmin]
    exact hnonneg r hr
  · intro r hr hle
    rw [hmin] at hle
    exact huniq r hr (le_antisymm hle (hnonneg r hr))
  · exact mul_pos hg hv
  · simp [gaugeMass]

end Frontier

