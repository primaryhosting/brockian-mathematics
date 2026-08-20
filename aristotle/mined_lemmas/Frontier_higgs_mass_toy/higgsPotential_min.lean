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

/-- Mexican-hat (abelian Higgs) potential for a radial scalar field profile `r = |φ|`,
with quartic coupling `lam` and symmetry-breaking scale `v`:
`V(r) = lam * (r² - v²)²`. -/

lemma higgsPotential_min (lam v : ℝ) (hlam : 0 < lam) :
    (∀ r : ℝ, higgsPotential lam v v ≤ higgsPotential lam v r) ∧
      ∀ r : ℝ, higgsPotential lam v r = higgsPotential lam v v → r ^ 2 = v ^ 2 := by
  have hv : higgsPotential lam v v = 0 := by
    unfold higgsPotential; ring
  constructor
  · intro r
    rw [hv]
    unfold higgsPotential
    positivity
  · intro r hr
    rw [hv] at hr
    unfold higgsPotential at hr
    have h : (r ^ 2 - v ^ 2) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hr with h | h
      · exact absurd h (ne_of_gt hlam)
      · exact h
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    linarith

/-- **Abelian Higgs toy model: spontaneous symmetry breaking gives the gauge boson a mass.**

With quartic coupling `lam > 0`, symmetry-breaking scale `v > 0` and gauge coupling `e ≠ 0`:

1. the symmetric configuration `r = 0` is *not* a minimum of the potential (the potential
   is strictly lower at `r = v`), and there the gauge boson is massless;
2. `r = v` is a global minimum of the potential;
3. every global minimum `r` produces the same, strictly positive gauge boson mass squared
   `e² v²`, realized by the mass `m_A = |e| v > 0`.
-/
