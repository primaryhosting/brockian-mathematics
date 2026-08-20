/-
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
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

namespace QPhys

/-- The partial derivative `∂L/∂q` of a one-dimensional Lagrangian
`L : position → velocity → time → ℝ`. -/

noncomputable def dLdq (L : ℝ → ℝ → ℝ → ℝ) (q v t : ℝ) : ℝ := deriv (fun x => L x v t) q

/-- The partial derivative `∂L/∂v` of a one-dimensional Lagrangian
`L : position → velocity → time → ℝ`; evaluated along a trajectory this is the
canonical momentum. -/

theorem dLdq_eq_zero_of_translation_invariant
    (L : ℝ → ℝ → ℝ → ℝ) (hinv : ∀ a x v t : ℝ, L (x + a) v t = L x v t)
    (q v t : ℝ) : dLdq L q v t = 0 := by
  have hconst : (fun x : ℝ => L x v t) = fun _ : ℝ => L 0 v t := by
    funext x
    have h := hinv x 0 v t
    simpa using h
  simp [dLdq, hconst]

/-- **Noether's theorem for spatial translations (1D).**
If the Lagrangian `L` is invariant under translations of the position variable
(`L (x + a) v t = L x v t`), and the trajectory `q` satisfies the Euler-Lagrange
equation `d/dt (∂L/∂v) = ∂L/∂q` along its path, then the canonical momentum
`p t = ∂L/∂v (q t, q' t, t)` is conserved. -/
