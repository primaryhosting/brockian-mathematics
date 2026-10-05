/-
# Higgs Mass Toy
Category: Frontier Physics
Target: Frontier.higgs_mass_toy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The "Mexican hat" scalar potential of the abelian Higgs toy model,
written in terms of the modulus `r = |φ|` of the complex scalar field:
`V(r) = lam * (r² - v²)²`. -/

lemma gaugeKinetic_iterated (g v A : ℝ) :
    ∀ n : ℕ, ∀ h : ℝ,
      gaugeKinetic g (v + h / 2 ^ n) A - gaugeMassSq g v * A ^ 2
        = (2 * g ^ 2 * v * (h / 2 ^ n) + g ^ 2 * (h / 2 ^ n) ^ 2) * A ^ 2 := by
  intro n
  induction n with
  | zero =>
      intro h
      have := gaugeKinetic_expansion g v h A
      simp only [pow_zero, div_one]
      rw [this]; ring
  | succ k ih =>
      intro h
      have := ih (h / 2)
      have hrw : h / 2 / 2 ^ k = h / 2 ^ (k + 1) := by
        rw [pow_succ]; ring
      rwa [hrw] at this

/--
**Higgs mass toy model (abelian Higgs).**

In the abelian Higgs model with Mexican-hat potential `V(r) = λ (r² - v²)²`
and gauge kinetic term `|D_μ φ|² ⊇ g² r² A²`, spontaneous symmetry breaking
(`λ > 0`, `v > 0`) has the following consequences:

1. `r = v` is a global minimum of `V`, with `V(v) = 0`, and it is the unique
   minimum up to `r² = v²`;
2. `V'(v) = 0`, so the vacuum is stationary;
3. `V''(v) = 8 λ v² = m_h² > 0`: the radial excitation is a massive Higgs boson;
4. expanding `r = v + h` in the gauge kinetic term produces the mass term
   `m_A² A²` with `m_A² = g² v² > 0` for `g ≠ 0`: **the gauge boson has become
   massive**;
5. by contrast in the unbroken vacuum `v = 0` the gauge boson mass vanishes.
-/
