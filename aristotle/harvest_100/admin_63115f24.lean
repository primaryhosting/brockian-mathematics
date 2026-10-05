import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

/-- The Brillouin torus, modelled as the fundamental domain `[0, 2π] × [0, 2π]` in `ℝ × ℝ`. -/
def brillouinZone : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) (2 * π) ×ˢ Set.Icc (0 : ℝ) (2 * π)

/-- Physical constants entering the quantum of conductance `e²/h`. -/
structure PhysConst where
  /-- Elementary charge. -/
  e : ℝ
  /-- Planck's constant. -/
  h : ℝ
  /-- Planck's constant is positive. -/
  h_pos : 0 < h

/-- The conductance quantum `e²/h`. -/
noncomputable def PhysConst.quantum (c : PhysConst) : ℝ := c.e ^ 2 / c.h

lemma PhysConst.quantum_nonneg (c : PhysConst) : 0 ≤ c.quantum :=
  div_nonneg (sq_nonneg _) c.h_pos.le

/--
A two-dimensional band insulator, described by the Berry curvature `berry` of the
occupied Bloch band over the Brillouin torus, together with its (integer) Chern number.

The defining property of the Chern number is the quantization of the integrated
Berry curvature: `∫_BZ F = 2π · C`.
-/
structure BandInsulator where
  /-- Berry curvature of the occupied band. -/
  berry : ℝ × ℝ → ℝ
  /-- The first Chern number of the Bloch bundle of the occupied band. -/
  chern : ℤ
  /-- Quantization of the integrated Berry curvature. -/
  quantized :
    (∫ k in brillouinZone, berry k) = 2 * π * (chern : ℝ)

/--
The zero-temperature Hall conductance predicted by linear response (Kubo formula):
the conductance quantum times the Berry curvature integrated over the Brillouin zone,
normalized by `2π`.
-/
noncomputable def hallConductance (c : PhysConst) (B : BandInsulator) : ℝ :=
  c.quantum * ((1 / (2 * π)) * ∫ k in brillouinZone, B.berry k)

/-- The TKNN formula: the Hall conductance equals the Chern number times `e²/h`. -/
theorem hallConductance_eq (c : PhysConst) (B : BandInsulator) :
    hallConductance c B = (B.chern : ℝ) * c.quantum := by
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [hallConductance, B.quantized]
  field_simp

/-- The integral of a constant Berry curvature over the Brillouin zone. -/
lemma setIntegral_const_brillouinZone (v : ℝ) :
    (∫ _k in brillouinZone, v) = (2 * π) ^ 2 * v := by
  have h : (0 : ℝ) ≤ 2 * π - 0 := by simp; positivity
  rw [brillouinZone, MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, Real.volume_Icc,
    ← ENNReal.ofReal_mul h, ENNReal.toReal_ofReal (by nlinarith)]
  simp only [smul_eq_mul]
  ring

/-- A model band insulator with constant Berry curvature realizing any prescribed Chern
number `n`; this shows the hypotheses of `Frontier.tknn_chern_hall` are non-vacuous. -/
noncomputable def constantCurvatureModel (n : ℤ) : BandInsulator where
  berry := fun _ => (n : ℝ) / (2 * π)
  chern := n
  quantized := by
    have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    rw [setIntegral_const_brillouinZone]
    field_simp

@[simp] lemma constantCurvatureModel_chern (n : ℤ) : (constantCurvatureModel n).chern = n := rfl

/--
**TKNN (Thouless–Kohmoto–Nightingale–den Nijs).**

For a two-dimensional band insulator with Berry curvature `B.berry` and Chern number
`B.chern`, the Hall conductance is exactly quantized:

* it equals the Chern number times the conductance quantum `e²/h`;
* in particular it is an integer multiple of `e²/h`;
* and it obeys the dichotomy: either the Chern number vanishes and the Hall conductance
  is zero, or the Chern number is nonzero and the Hall conductance has magnitude at
  least one conductance quantum.
-/
theorem tknn_chern_hall (c : PhysConst) (B : BandInsulator) :
    hallConductance c B = (B.chern : ℝ) * c.quantum ∧
    (∃ n : ℤ, hallConductance c B = (n : ℝ) * c.quantum) ∧
    (B.chern = 0 → hallConductance c B = 0) ∧
    (B.chern ≠ 0 → c.quantum ≤ |hallConductance c B|) := by
  have hmain : hallConductance c B = (B.chern : ℝ) * c.quantum := hallConductance_eq c B
  refine ⟨hmain, ⟨B.chern, hmain⟩, ?_, ?_⟩
  · intro h0
    rw [hmain, h0]
    simp
  · intro hne
    rw [hmain, abs_mul, abs_of_nonneg c.quantum_nonneg]
    have h1 : (1 : ℝ) ≤ |(B.chern : ℝ)| := by
      have : (1 : ℤ) ≤ |B.chern| := Int.one_le_abs (by omega)
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|B.chern| : ℤ) : ℝ) := by exact_mod_cast this
        _ = |(B.chern : ℝ)| := by push_cast [Int.cast_abs]; ring
    nlinarith [c.quantum_nonneg, abs_nonneg ((B.chern : ℝ))]

end Frontier

