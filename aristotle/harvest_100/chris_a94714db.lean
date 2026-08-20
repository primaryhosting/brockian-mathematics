/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Set Topology

namespace Phys

/-- The auxiliary "virial current"
`F x = x * ψ' x ^ 2 - x * (V x - E) * ψ x ^ 2 + ψ x * ψ' x`,
whose derivative is exactly `2 * ψ' x ^ 2 - x * V' x * ψ x ^ 2` for a solution of the
stationary Schrödinger equation. -/
noncomputable def virialCurrent (psi psi1 V : ℝ → ℝ) (E : ℝ) : ℝ → ℝ := fun x =>
  x * psi1 x ^ 2 - x * (V x - E) * psi x ^ 2 + psi x * psi1 x

/-- Pointwise Lagrange-type identity: for a solution of `-ψ'' + V ψ = E ψ`, the virial current
has derivative `2 ψ'² - x V' ψ²`. -/
theorem hasDerivAt_virialCurrent
    (psi psi1 psi2 V V1 : ℝ → ℝ) (E : ℝ)
    (hpsi : ∀ x, HasDerivAt psi (psi1 x) x)
    (hpsi1 : ∀ x, HasDerivAt psi1 (psi2 x) x)
    (hV : ∀ x, HasDerivAt V (V1 x) x)
    (hSch : ∀ x, -psi2 x + V x * psi x = E * psi x) (x : ℝ) :
    HasDerivAt (virialCurrent psi psi1 V E)
      (2 * psi1 x ^ 2 - x * V1 x * psi x ^ 2) x := by
  have hpsi2eq : psi2 x = (V x - E) * psi x := by
    linarith [hSch x]
  have h1 : HasDerivAt (fun y => y * psi1 y ^ 2)
      (1 * psi1 x ^ 2 + x * (2 * psi1 x * psi2 x)) x := by
    have hsq : HasDerivAt (fun y => psi1 y ^ 2) (2 * psi1 x * psi2 x) x := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using (hpsi1 x).pow 2
    exact (hasDerivAt_id x).mul hsq
  have h2 : HasDerivAt (fun y => y * (V y - E) * psi y ^ 2)
      ((1 * (V x - E) + x * V1 x) * psi x ^ 2
        + x * (V x - E) * (2 * psi x * psi1 x)) x := by
    have hVE : HasDerivAt (fun y => V y - E) (V1 x) x := (hV x).sub_const E
    have ha : HasDerivAt (fun y => y * (V y - E)) (1 * (V x - E) + x * V1 x) x :=
      (hasDerivAt_id x).mul hVE
    have hsq : HasDerivAt (fun y => psi y ^ 2) (2 * psi x * psi1 x) x := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using (hpsi x).pow 2
    exact ha.mul hsq
  have h3 : HasDerivAt (fun y => psi y * psi1 y) (psi1 x * psi1 x + psi x * psi2 x) x :=
    (hpsi x).mul (hpsi1 x)
  have := (h1.sub h2).add h3
  convert this using 1
  rw [hpsi2eq]
  ring

/-- **Quantum virial theorem** (one dimension, units in which the Hamiltonian is
`H = -d²/dx² + V`).

Let `psi` be a bound stationary state: a twice-differentiable real wave function with
`psi1 = psi'`, `psi2 = psi''`, satisfying the time-independent Schrödinger equation
`-psi'' + V psi = E psi` for a differentiable potential `V` with derivative `V1 = V'`.
Assume the kinetic and virial densities are integrable, and that the boundary term
`virialCurrent` (which involves `x psi'^2`, `x (V - E) psi^2` and `psi psi'`) vanishes at
`±∞` — this is what "bound state" provides.

Then `2⟨T⟩ = ⟨x ∂V/∂x⟩`, where `⟨T⟩ = ∫ psi'^2` (the expectation of `-d²/dx²`) and
`⟨x V'⟩ = ∫ x V' psi^2`
(no normalization of `psi` is needed for this identity). -/
theorem virial_theorem
    (psi psi1 psi2 V V1 : ℝ → ℝ) (E : ℝ)
    (hpsi : ∀ x, HasDerivAt psi (psi1 x) x)
    (hpsi1 : ∀ x, HasDerivAt psi1 (psi2 x) x)
    (hV : ∀ x, HasDerivAt V (V1 x) x)
    (hSch : ∀ x, -psi2 x + V x * psi x = E * psi x)
    (hT : Integrable (fun x => psi1 x ^ 2))
    (hW : Integrable (fun x => x * V1 x * psi x ^ 2))
    (hTop : Tendsto (virialCurrent psi psi1 V E) atTop (𝓝 0))
    (hBot : Tendsto (virialCurrent psi psi1 V E) atBot (𝓝 0)) :
    2 * (∫ x, psi1 x ^ 2) = ∫ x, x * V1 x * psi x ^ 2 := by
  set g : ℝ → ℝ := fun x => 2 * psi1 x ^ 2 - x * V1 x * psi x ^ 2 with hg
  have hgint : Integrable g := (hT.const_mul 2).sub hW
  have hderiv := hasDerivAt_virialCurrent psi psi1 psi2 V V1 E hpsi hpsi1 hV hSch
  have hIic : (∫ x in Iic (0 : ℝ), g x) = virialCurrent psi psi1 V E 0 - 0 :=
    integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hderiv x) hgint.integrableOn hBot
  have hIoi : (∫ x in Ioi (0 : ℝ), g x) = 0 - virialCurrent psi psi1 V E 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hderiv x) hgint.integrableOn hTop
  have hsum : (∫ x, g x) = 0 := by
    rw [← intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ)) hgint.integrableOn
      hgint.integrableOn, hIic, hIoi]
    ring
  have hsplit : (∫ x, g x) = 2 * (∫ x, psi1 x ^ 2) - ∫ x, x * V1 x * psi x ^ 2 := by
    rw [hg, integral_sub (hT.const_mul 2) hW, integral_const_mul]
  linarith [hsum, hsplit]

/-! ## Non-vacuity: the harmonic-oscillator ground state

The hypotheses of `Phys.virial_theorem` are satisfied by a genuine bound state: for the
Hamiltonian `H = -d²/dx² + x²` the ground state is `ψ x = exp (-x²/2)` with energy `E = 1`.
-/

private theorem exp_sq_aux (x : ℝ) : (Real.exp (-x ^ 2 / 2)) ^ 2 = Real.exp (-1 * x ^ 2) := by
  rw [sq, ← Real.exp_add]; ring_nf

private theorem integrable_sq_mul_gaussian :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-1 * x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := 2) (by norm_num)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  have hx : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by rw [← Real.rpow_natCast x 2]; norm_num
  show x ^ (2 : ℝ) * Real.exp (-1 * x ^ 2) = x ^ 2 * Real.exp (-1 * x ^ 2)
  rw [hx]

/-- Instance of the virial theorem for the harmonic oscillator `H = -d²/dx² + x²` with ground
state `ψ x = exp (-x²/2)`, energy `E = 1`: it shows that the hypotheses of
`Phys.virial_theorem` are not vacuous. -/
theorem virial_theorem_harmonic_oscillator :
    2 * (∫ x : ℝ, (-x * Real.exp (-x ^ 2 / 2)) ^ 2)
      = ∫ x : ℝ, x * (2 * x) * (Real.exp (-x ^ 2 / 2)) ^ 2 := by
  have hzero : virialCurrent (fun x : ℝ => Real.exp (-x ^ 2 / 2))
      (fun x : ℝ => -x * Real.exp (-x ^ 2 / 2)) (fun x : ℝ => x ^ 2) 1 = fun _ => (0 : ℝ) := by
    funext x
    simp only [virialCurrent]
    ring
  have hinner : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    intro x
    have h := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert h using 1
    ring
  refine virial_theorem (fun x => Real.exp (-x ^ 2 / 2)) (fun x => -x * Real.exp (-x ^ 2 / 2))
    (fun x => (x ^ 2 - 1) * Real.exp (-x ^ 2 / 2)) (fun x => x ^ 2) (fun x => 2 * x) 1
    (fun x => by simpa [mul_comm] using (hinner x).exp) (fun x => ?_)
    (fun x => by simpa using hasDerivAt_pow 2 x) (fun x => by ring) ?_ ?_ ?_ ?_
  · have h : HasDerivAt (fun y : ℝ => -y * Real.exp (-y ^ 2 / 2))
        (-1 * Real.exp (-x ^ 2 / 2) + -x * (Real.exp (-x ^ 2 / 2) * -x)) x :=
      ((hasDerivAt_id x).neg).mul (hinner x).exp
    convert h using 1
    ring
  · refine integrable_sq_mul_gaussian.congr (Filter.Eventually.of_forall fun x => ?_)
    show x ^ 2 * Real.exp (-1 * x ^ 2) = (-x * Real.exp (-x ^ 2 / 2)) ^ 2
    rw [mul_pow, neg_sq, exp_sq_aux]
  · refine (integrable_sq_mul_gaussian.const_mul 2).congr (Filter.Eventually.of_forall fun x => ?_)
    show 2 * (x ^ 2 * Real.exp (-1 * x ^ 2)) = x * (2 * x) * (Real.exp (-x ^ 2 / 2)) ^ 2
    rw [exp_sq_aux]; ring
  · rw [hzero]; exact tendsto_const_nhds
  · rw [hzero]; exact tendsto_const_nhds

end Phys

import Mathlib

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

