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
