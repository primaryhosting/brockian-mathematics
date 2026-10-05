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

import Mathlib

/-!
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

open Set MeasureTheory

namespace Brockian.Weyl.DeficiencyODE

/-- **Weak regularity** of a potential `q : ℝ → ℂ`: `q` is bounded on every compact interval.
This is much weaker than continuity of `q`; it is exactly what is needed to run the Gronwall
argument behind uniqueness for the Sturm–Liouville system. -/

theorem eq_zero_of_isSolution_of_apply_zero (hq : WeaklyRegular q) {w : ℝ → ℂ × ℂ}
    (hw : IsSolution q z w) (h0 : w 0 = 0) : w = 0 := by
  funext t
  obtain ⟨R, hRt, hR0⟩ : ∃ R : ℝ, |t| < R ∧ (0:ℝ) < R :=
    ⟨|t| + 1, by linarith, by positivity⟩
  obtain ⟨C, hC⟩ := hq (-R) R
  have hmem : t ∈ Set.Icc (-R) R := by
    constructor
    · linarith [neg_abs_le t]
    · linarith [le_abs_self t]
  have key : Set.EqOn w 0 (Set.Icc (-R) R) := by
    refine ODE_solution_unique_of_mem_Icc (v := sturmField q z) (s := fun _ => Set.univ)
      (K := Real.toNNReal (max 1 (C + ‖z‖))) (t₀ := 0)
      (fun s hs => lipschitz_sturmField hC (Set.mem_Icc_of_Ioo hs))
      ⟨by linarith, hR0⟩
      (fun s _ => (hw s).continuousAt.continuousWithinAt)
      (fun s _ => hw s) (fun _ _ => Set.mem_univ _)
      continuousOn_const
      (fun s _ => by simpa [sturmField] using (hasDerivAt_const s (0 : ℂ × ℂ)))
      (fun _ _ => Set.mem_univ _) (by simpa using h0)
  simpa using key hmem

end Uniqueness

/-- **Deficiency represents the ODE, for weakly regular potentials.**

For a potential `q` bounded on compact intervals (weak regularity) and any spectral parameter
`z : ℂ`, every element of the deficiency space of the Sturm–Liouville expression
`-u'' + q u = z u` on the half line is faithfully represented by its Cauchy data
`(u 0, u' 0) ∈ ℂ²`; consequently the deficiency space has rank at most `2`.

No hypothesis beyond weak regularity of `q` is assumed. -/
