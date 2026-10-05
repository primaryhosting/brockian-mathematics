/-
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
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

namespace Phys

/-- The Unruh temperature `T = ℏ a / (2 π c k_B)` seen by an observer with proper
acceleration `a`, in terms of the reduced Planck constant `hbar`, the speed of light `c`
and Boltzmann's constant `kB`. -/
noncomputable def unruhTemperature (hbar a c kB : ℝ) : ℝ :=
  hbar * a / (2 * Real.pi * c * kB)

/-- The Euclidean (imaginary-time) period of a Rindler observer with proper
acceleration `a`, i.e. `β = 2 π c / a` measured in units of `hbar / kB`. -/
noncomputable def rindlerPeriod (a c : ℝ) : ℝ := 2 * Real.pi * c / a

/-- Bose–Einstein occupation number at temperature `T` for a mode of angular frequency `ω`. -/
noncomputable def boseEinstein (hbar kB T omega : ℝ) : ℝ :=
  1 / (Real.exp (hbar * omega / (kB * T)) - 1)

/-- **The Unruh effect.**

For an observer undergoing uniform proper acceleration `a` (with `hbar, a, c, kB > 0`),
the Unruh temperature is
`T = ℏ a / (2 π c k_B)`,
and it is characterised by the following equivalent properties:

1. `T > 0`;
2. the thermal energy is `k_B T = ℏ a / (2 π c)`, i.e. `T` is the unique temperature whose
   thermal energy equals `ℏ a / (2 π c)`;
3. the Boltzmann factor at temperature `T` for a mode of angular frequency `ω` coincides with
   the Bogoliubov/Rindler factor `exp (-2 π c ω / a)` obtained from the periodicity of the
   Euclidean Rindler time, for every `ω`; equivalently `ℏ / (k_B T) = β` with
   `β = 2 π c / a` the Rindler period;
4. consequently the Rindler mode occupation numbers are exactly the Bose–Einstein
   occupation numbers at temperature `T`.
-/
theorem unruh_effect (hbar a c kB : ℝ)
    (hbar_pos : 0 < hbar) (ha : 0 < a) (hc : 0 < c) (hkB : 0 < kB) :
    let T : ℝ := unruhTemperature hbar a c kB
    0 < T ∧
    T = hbar * a / (2 * Real.pi * c * kB) ∧
    kB * T = hbar * a / (2 * Real.pi * c) ∧
    (∀ T' : ℝ, kB * T' = hbar * a / (2 * Real.pi * c) → T' = T) ∧
    hbar / (kB * T) = rindlerPeriod a c ∧
    (∀ omega : ℝ, Real.exp (-(hbar * omega) / (kB * T))
        = Real.exp (-(2 * Real.pi * c * omega) / a)) ∧
    (∀ omega : ℝ, boseEinstein hbar kB T omega
        = 1 / (Real.exp (2 * Real.pi * c * omega / a) - 1)) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hden : (0:ℝ) < 2 * Real.pi * c * kB := by positivity
  intro T
  have hT : T = hbar * a / (2 * Real.pi * c * kB) := rfl
  have hTpos : 0 < T := by
    rw [hT]; positivity
  have hkT : kB * T = hbar * a / (2 * Real.pi * c) := by
    rw [hT]
    field_simp
  have hratio : ∀ omega : ℝ, hbar * omega / (kB * T) = 2 * Real.pi * c * omega / a := by
    intro omega
    rw [hkT]
    rw [div_div_eq_mul_div]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  refine ⟨hTpos, hT, hkT, ?_, ?_, ?_, ?_⟩
  · intro T' hT'
    have : kB * T' = kB * T := by rw [hT', hkT]
    exact mul_left_cancel₀ (ne_of_gt hkB) this
  · have h1 : hbar / (kB * T) = hbar * 1 / (kB * T) := by ring_nf
    have := hratio 1
    rw [h1, this]
    unfold rindlerPeriod
    ring_nf
  · intro omega
    congr 1
    have := hratio omega
    field_simp at this ⊢
    linarith [this]
  · intro omega
    unfold boseEinstein
    rw [hratio omega]

end Phys

