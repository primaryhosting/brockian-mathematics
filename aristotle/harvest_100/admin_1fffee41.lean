import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open MeasureTheory

/-- The Brillouin zone, modelled as the unit square `[0,1] × [0,1]` in quasi-momentum
coordinates (the fundamental domain of the momentum-space torus). -/
def brillouinZone : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- The (first) Chern number of a Bloch band with Berry curvature `F` on the Brillouin zone:
the total Berry flux divided by `2π`. -/
noncomputable def chernNumber (F : ℝ × ℝ → ℝ) : ℝ :=
  (∫ p in brillouinZone, F p) / (2 * Real.pi)

/-- The zero-temperature Hall conductance of a filled band with Berry curvature `F`,
in terms of the elementary charge `e` and Planck's constant `h`: the Kubo formula
expresses it as `(e²/h)` times the Berry flux over `2π`. -/
noncomputable def hallConductance (e h : ℝ) (F : ℝ × ℝ → ℝ) : ℝ :=
  (e ^ 2 / h) * chernNumber F

/-- **TKNN (Thouless–Kohmoto–Nightingale–den Nijs) quantization.**
If the Berry flux of a filled Bloch band over the Brillouin zone is quantized,
`∫_BZ F = 2π C` with `C : ℤ`, then the integer-quantum-Hall conductance equals the
Chern number `C` times the conductance quantum `e²/h`. -/
theorem tknn_chern_hall (e h : ℝ) (F : ℝ × ℝ → ℝ) (C : ℤ)
    (hflux : ∫ p in brillouinZone, F p = 2 * Real.pi * (C : ℝ)) :
    hallConductance e h F = (C : ℝ) * (e ^ 2 / h) := by
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  unfold hallConductance chernNumber
  rw [hflux, mul_comm (2 * Real.pi) (C : ℝ), mul_div_assoc, div_self hpi, mul_one,
    mul_comm]

/-- Consistency check: a band with uniform Berry curvature `2π` over the unit-square
Brillouin zone has Chern number `1`, and hence Hall conductance exactly `e²/h`. -/
theorem tknn_chern_hall_unit_curvature (e h : ℝ) :
    hallConductance e h (fun _ => 2 * Real.pi) = e ^ 2 / h := by
  have hvol : volume brillouinZone = 1 := by
    rw [brillouinZone, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
    norm_num
  have hflux : ∫ _ in brillouinZone, (2 * Real.pi) = 2 * Real.pi * ((1 : ℤ) : ℝ) := by
    rw [MeasureTheory.setIntegral_const, Measure.real, hvol]
    simp
  have := tknn_chern_hall e h (fun _ => 2 * Real.pi) 1 hflux
  simpa using this

end Frontier

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

