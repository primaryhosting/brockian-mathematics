/-
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ssh Winding Invariant
Category: Frontier Physics
Target: Frontier.ssh_winding_invariant
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

open Complex intervalIntegral

/-- The off-diagonal entry of the Bloch Hamiltonian of the Su–Schrieffer–Heeger (SSH) chain
with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w e^{i k}`.  The full Bloch Hamiltonian is the chiral (off-diagonal) matrix
`[[0, h(k)], [conj (h k), 0]]`, so the spectral gap is open at `k` iff `h k ≠ 0`. -/

theorem sign_const_of_ne_zero_on_Icc (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (0:ℝ) 1))
    (h0 : ∀ t ∈ Set.Icc (0:ℝ) 1, f t ≠ 0) :
    (f 0 < 0 ∧ f 1 < 0) ∨ (0 < f 0 ∧ 0 < f 1) := by
  have hz : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have ho : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  rcases lt_or_gt_of_ne (h0 0 hz) with hf0 | hf0
  · refine Or.inl ⟨hf0, ?_⟩
    rcases lt_or_gt_of_ne (h0 1 ho) with hf1 | hf1
    · exact hf1
    · exfalso
      obtain ⟨c, hc, hc0⟩ :=
        intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hf ⟨hf0.le, hf1.le⟩
      exact h0 c hc hc0
  · refine Or.inr ⟨hf0, ?_⟩
    rcases lt_or_gt_of_ne (h0 1 ho) with hf1 | hf1
    · exfalso
      obtain ⟨c, hc, hc0⟩ :=
        intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hf ⟨hf1.le, hf0.le⟩
      exact h0 c hc hc0
    · exact hf1

/-- **Homotopy invariance of the SSH winding number.**  Along any continuous path of SSH
parameters `t ↦ (v t, w t)` that stays gapped (`w t > 0` and `|v t| ≠ w t` for all `t ∈ [0,1]`),
the winding number is unchanged.  This is the precise sense in which the winding number is a
topological invariant of the gapped SSH chain. -/
