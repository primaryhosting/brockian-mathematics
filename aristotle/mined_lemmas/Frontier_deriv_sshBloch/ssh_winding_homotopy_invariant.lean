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

theorem ssh_winding_homotopy_invariant (v w : ℝ → ℝ)
    (hv : ContinuousOn v (Set.Icc (0:ℝ) 1)) (hw : ContinuousOn w (Set.Icc (0:ℝ) 1))
    (hwpos : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < w t)
    (hgap : ∀ t ∈ Set.Icc (0:ℝ) 1, |v t| ≠ w t) :
    sshWinding (v 0) (w 0) = sshWinding (v 1) (w 1) := by
  have hz : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have ho : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hcont : ContinuousOn (fun t => |v t| - w t) (Set.Icc (0:ℝ) 1) := (hv.abs).sub hw
  have hne : ∀ t ∈ Set.Icc (0:ℝ) 1, |v t| - w t ≠ 0 := fun t ht =>
    sub_ne_zero_of_ne (hgap t ht)
  rcases sign_const_of_ne_zero_on_Icc _ hcont hne with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [sshWinding_topological _ _ (by linarith [h0] : |v 0| < w 0),
      sshWinding_topological _ _ (by linarith [h1] : |v 1| < w 1)]
  · rw [sshWinding_trivial _ _ (hwpos 0 hz) (by linarith [h0] : w 0 < |v 0|),
      sshWinding_trivial _ _ (hwpos 1 ho) (by linarith [h1] : w 1 < |v 1|)]

end Frontier

