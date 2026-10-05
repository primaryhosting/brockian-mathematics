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
noncomputable def higgsPotential (lam v r : ℝ) : ℝ := lam * (r ^ 2 - v ^ 2) ^ 2

/-- The gauge-invariant kinetic term `|D_μ φ|²` of the abelian Higgs model,
restricted to a constant modulus `r` and a constant gauge field `A`,
contributes `g² r² A²` to the Lagrangian. -/
noncomputable def gaugeKinetic (g r A : ℝ) : ℝ := g ^ 2 * r ^ 2 * A ^ 2

/-- The squared mass acquired by the gauge boson after spontaneous symmetry
breaking around the vacuum `r = v`, i.e. `m_A² = g² v²`. -/
noncomputable def gaugeMassSq (g v : ℝ) : ℝ := g ^ 2 * v ^ 2

/-- The squared mass of the physical (radial) Higgs excitation,
`m_h² = V''(v) = 8 λ v²`. -/
noncomputable def higgsMassSq (lam v : ℝ) : ℝ := 8 * lam * v ^ 2

section Potential

variable (lam v : ℝ)

lemma higgsPotential_vacuum : higgsPotential lam v v = 0 := by
  simp [higgsPotential]

lemma higgsPotential_nonneg (hlam : 0 ≤ lam) (r : ℝ) : 0 ≤ higgsPotential lam v r := by
  have : (0:ℝ) ≤ (r ^ 2 - v ^ 2) ^ 2 := sq_nonneg _
  exact mul_nonneg hlam this

/-- `r = v` is a global minimum of the Mexican-hat potential. -/
lemma higgsPotential_min (hlam : 0 ≤ lam) (r : ℝ) :
    higgsPotential lam v v ≤ higgsPotential lam v r := by
  rw [higgsPotential_vacuum]
  exact higgsPotential_nonneg lam v hlam r

/-- The strict-minimum statement: for `lam > 0` and `v > 0`, the potential is
strictly larger than its vacuum value away from `r = ±v`. -/
lemma higgsPotential_strict_min (hlam : 0 < lam) (r : ℝ) (hr : r ^ 2 ≠ v ^ 2) :
    higgsPotential lam v v < higgsPotential lam v r := by
  rw [higgsPotential_vacuum]
  have h : (0:ℝ) < (r ^ 2 - v ^ 2) ^ 2 := by
    have : r ^ 2 - v ^ 2 ≠ 0 := sub_ne_zero_of_ne hr
    positivity
  exact mul_pos hlam h

lemma deriv_higgsPotential (r : ℝ) :
    deriv (fun x : ℝ => higgsPotential lam v x) r = 4 * lam * r * (r ^ 2 - v ^ 2) := by
  have h : (fun x : ℝ => higgsPotential lam v x)
      = fun x : ℝ => lam * (x ^ 2 - v ^ 2) ^ 2 := rfl
  rw [h]
  have : deriv (fun x : ℝ => lam * (x ^ 2 - v ^ 2) ^ 2) r
      = lam * deriv (fun x : ℝ => (x ^ 2 - v ^ 2) ^ 2) r := by
    apply deriv_const_mul
    fun_prop
  rw [this]
  have hd : HasDerivAt (fun x : ℝ => (x ^ 2 - v ^ 2) ^ 2) (2 * (r ^ 2 - v ^ 2) * (2 * r)) r := by
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2 - v ^ 2) (2 * r) r := by
      simpa using ((hasDerivAt_pow 2 r).sub_const (v ^ 2))
    simpa using h1.pow 2
  rw [hd.deriv]
  ring

/-- The vacuum is a stationary point of the potential. -/
lemma deriv_higgsPotential_vacuum :
    deriv (fun x : ℝ => higgsPotential lam v x) v = 0 := by
  rw [deriv_higgsPotential]
  ring

/-- The curvature of the potential at the vacuum is the physical Higgs mass squared. -/
lemma deriv2_higgsPotential_vacuum :
    deriv (deriv fun x : ℝ => higgsPotential lam v x) v = higgsMassSq lam v := by
  have h : (deriv fun x : ℝ => higgsPotential lam v x)
      = fun r : ℝ => 4 * lam * r * (r ^ 2 - v ^ 2) := by
    funext r; exact deriv_higgsPotential lam v r
  rw [h]
  have hd : HasDerivAt (fun r : ℝ => 4 * lam * r * (r ^ 2 - v ^ 2))
      (4 * lam * (3 * v ^ 2 - v ^ 2)) v := by
    have h1 : HasDerivAt (fun r : ℝ => 4 * lam * r) (4 * lam) v := by
      simpa using (hasDerivAt_id v).const_mul (4 * lam)
    have h2 : HasDerivAt (fun r : ℝ => r ^ 2 - v ^ 2) (2 * v) v := by
      simpa using ((hasDerivAt_pow 2 v).sub_const (v ^ 2))
    have := h1.mul h2
    convert this using 1
    ring
  rw [hd.deriv, higgsMassSq]
  ring

end Potential

section GaugeMass

variable (g v : ℝ)

/-- Expanding the gauge kinetic term about the vacuum `r = v + h` isolates a
mass term `m_A² A²` for the gauge field, plus interactions of order `h`. -/
lemma gaugeKinetic_expansion (h A : ℝ) :
    gaugeKinetic g (v + h) A
      = gaugeMassSq g v * A ^ 2 + (2 * g ^ 2 * v * h + g ^ 2 * h ^ 2) * A ^ 2 := by
  simp only [gaugeKinetic, gaugeMassSq]
  ring

/-- In the broken phase (`v ≠ 0`) with nonzero gauge coupling the gauge boson
is massive. -/
lemma gaugeMassSq_pos (hg : g ≠ 0) (hv : v ≠ 0) : 0 < gaugeMassSq g v := by
  have h1 : 0 < g ^ 2 := by positivity
  have h2 : 0 < v ^ 2 := by positivity
  exact mul_pos h1 h2

/-- In the symmetric phase (`v = 0`) the gauge boson stays massless. -/
lemma gaugeMassSq_symmetric : gaugeMassSq g 0 = 0 := by
  simp [gaugeMassSq]

end GaugeMass

/-- Iterating the expansion: the `n`-th order Taylor coefficient structure of the
gauge kinetic term. Concretely, for every `n`, the constant-`A` gauge kinetic
energy evaluated at the rescaled fluctuation `h/2^n` still contains exactly the
mass term `m_A² A²` at zeroth order in the fluctuation. This is proved by
induction on `n`. -/
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
theorem higgs_mass_toy (lam v g : ℝ) (hlam : 0 < lam) (hv : 0 < v) (hg : g ≠ 0) :
    higgsPotential lam v v = 0
    ∧ (∀ r : ℝ, higgsPotential lam v v ≤ higgsPotential lam v r)
    ∧ (∀ r : ℝ, r ^ 2 ≠ v ^ 2 → higgsPotential lam v v < higgsPotential lam v r)
    ∧ deriv (fun x : ℝ => higgsPotential lam v x) v = 0
    ∧ deriv (deriv fun x : ℝ => higgsPotential lam v x) v = higgsMassSq lam v
    ∧ 0 < higgsMassSq lam v
    ∧ (∀ h A : ℝ, gaugeKinetic g (v + h) A
        = gaugeMassSq g v * A ^ 2 + (2 * g ^ 2 * v * h + g ^ 2 * h ^ 2) * A ^ 2)
    ∧ 0 < gaugeMassSq g v
    ∧ gaugeMassSq g 0 = 0 := by
  refine ⟨higgsPotential_vacuum lam v, fun r => higgsPotential_min lam v hlam.le r,
    fun r hr => higgsPotential_strict_min lam v hlam r hr,
    deriv_higgsPotential_vacuum lam v, deriv2_higgsPotential_vacuum lam v, ?_,
    fun h A => gaugeKinetic_expansion g v h A,
    gaugeMassSq_pos g v hg hv.ne', gaugeMassSq_symmetric g⟩
  have : 0 < v ^ 2 := by positivity
  simp only [higgsMassSq]
  positivity

end Frontier

