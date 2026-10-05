import Mathlib

/-!
# Psi Cubic Eq One Of Small
Category: A Assembly
Target: Zeta23Scaffold.psiCubic_eq_one_of_small
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Zeta23Scaffold

/-- The cubic weight `psi(m) = m/2 + (2m² - m³)/18 + (4/9)·[m = 1]` of the
preprint, SS7.5(g). -/
def psiCubic (m : ℕ) : ℚ :=
  (m : ℚ) / 2 + (2 * (m : ℚ) ^ 2 - (m : ℚ) ^ 3) / 18 + (if m = 1 then 4 / 9 else 0)

/-- The cubic weight attains the value `1` at `m = 1, 2, 3`. -/
theorem psiCubic_eq_one_of_small :
    psiCubic 1 = 1 ∧ psiCubic 2 = 1 ∧ psiCubic 3 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold psiCubic; norm_num

/-- Uniform restatement: `psiCubic m = 1` for every `m ∈ {1, 2, 3}`. -/
theorem psiCubic_eq_one_of_mem_small {m : ℕ} (hm : m = 1 ∨ m = 2 ∨ m = 3) :
    psiCubic m = 1 := by
  obtain rfl | rfl | rfl := hm
  · exact psiCubic_eq_one_of_small.1
  · exact psiCubic_eq_one_of_small.2.1
  · exact psiCubic_eq_one_of_small.2.2

end Zeta23Scaffold

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

