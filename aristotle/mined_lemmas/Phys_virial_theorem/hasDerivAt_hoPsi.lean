/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Statement: For a bound stationary state, 2⟨T⟩ = ⟨r·∇V⟩ (quantum virial theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology

namespace Phys

/-- **Auxiliary integration-by-parts fact.**  If `f` is everywhere differentiable with
integrable derivative `f'` and `f` tends to `0` at both ends of the real line, then the
integral of `f'` over `ℝ` vanishes. -/

theorem hasDerivAt_hoPsi (x : ℝ) : HasDerivAt hoPsi (hoDPsi x) x := by
  have h : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    have h2 := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert h2 using 1
    simp; ring
  have h3 := h.exp
  convert h3 using 1
  rw [hoDPsi]; ring

