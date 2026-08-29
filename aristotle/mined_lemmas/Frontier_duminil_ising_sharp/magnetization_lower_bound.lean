/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

/-!
## The finite-volume Ising model

We set up the ferromagnetic Ising model on a finite graph `G` at inverse temperature `β`
with external field `h`: spins `σ : V → Bool` with values `spinVal (σ x) ∈ {-1, +1}`,
Gibbs weights `exp (-β * energy + h * ∑ spins)`, and the associated expectations,
two-point functions and magnetisation.
-/

section IsingFinite

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The spin value `±1` attached to a Boolean spin variable. -/

theorem magnetization_lower_bound (mag : ℝ → ℝ) (betaC : ℝ) (hbc : 0 < betaC)
    (hcont : ContinuousOn mag (Set.Ici betaC))
    (hdiff : ∀ β ∈ Set.Ioi betaC, DifferentiableAt ℝ mag β)
    (hineq : ∀ β ∈ Set.Ioi betaC, (1 - mag β) / β ≤ deriv mag β)
    (hmag0 : 0 ≤ mag betaC) :
    ∀ β, betaC < β → (β - betaC) / β ≤ mag β := by
  set g : ℝ → ℝ := fun t => t * (1 - mag t) with hgdef
  have hderiv : ∀ x ∈ Set.Ioi betaC,
      HasDerivAt g (1 * (1 - mag x) + x * (0 - deriv mag x)) x := by
    intro x hx
    exact (hasDerivAt_id x).mul ((hasDerivAt_const x (1 : ℝ)).sub ((hdiff x hx).hasDerivAt))
  have hgc : ContinuousOn g (Set.Ici betaC) :=
    continuousOn_id.mul (continuousOn_const.sub hcont)
  have hganti : AntitoneOn g (Set.Ici betaC) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici _) hgc ?_ ?_
    · intro x hx
      rw [interior_Ici] at hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := lt_trans hbc hx
      have hkey : 1 - mag x ≤ x * deriv mag x := by
        have := hineq x hx
        rwa [div_le_iff₀ hx0, mul_comm] at this
      rw [(hderiv x hx).deriv]
      nlinarith
  intro β hβ
  have hβ0 : 0 < β := lt_trans hbc hβ
  have hle : g β ≤ g betaC :=
    hganti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hβ.le) hβ.le
  have hgc' : g betaC ≤ betaC := by
    have : betaC * (1 - mag betaC) ≤ betaC * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) hbc.le
    simpa [hgdef] using this
  have hfin : β * (1 - mag β) ≤ betaC := le_trans hle hgc'
  rw [div_le_iff₀ hβ0]
  nlinarith

/-- **Sharpness of the phase transition for the Ising model (Duminil-Copin).**

`corr β n` denotes the infinite-volume two-point function `⟨σ_0 σ_x⟩_β` at distance `n`
(a nonnegative quantity bounded by `1`, by Griffiths' inequality) and `mag β` denotes the
spontaneous magnetisation `⟨σ_0⟩_β^+`, with critical inverse temperature `betaC > 0`.

The two model-dependent inputs of the Duminil-Copin–Tassion proof are assumed:

* below `betaC`, the finite criterion `φ_β(S) < 1` gives a strict `L`-step contraction
  `corr β (n + L) ≤ c * corr β n` with `c < 1`;
* above `betaC`, the differential inequality `∂_β mag ≥ (1 - mag) / β` holds, together with
  continuity of `mag` up to `betaC` and nonnegativity at `betaC`.

The conclusion is sharpness: the transition at `betaC` is sharp, i.e. correlations decay
exponentially fast strictly below `betaC`, while the spontaneous magnetisation is strictly
positive — with the explicit mean-field lower bound `(β - betaC) / β` — strictly above
`betaC`. -/
