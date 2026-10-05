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

namespace QPhys

/-- If the Lagrangian is invariant under spatial translations, then its partial
derivative with respect to position vanishes identically. -/

theorem lagrangian_translation_invariant_partial_pos_zero
    (L Lq : ℝ → ℝ → ℝ)
    (hinv : ∀ a q v, L (q + a) v = L q v)
    (hLq : ∀ q v, HasDerivAt (fun x => L x v) (Lq q v) q) :
    ∀ q v, Lq q v = 0 := by
  intro q v
  have hconst : (fun x : ℝ => L x v) = fun _ : ℝ => L 0 v := by
    funext x
    have := hinv x 0 v
    simpa using this
  have h0 : HasDerivAt (fun x : ℝ => L x v) 0 q := by
    rw [hconst]
    exact hasDerivAt_const q (L 0 v)
  exact (hLq q v).unique h0

/--
**Noether's theorem for spatial translations (one dimension).**

Let `L : ℝ → ℝ → ℝ` be a Lagrangian `L q v`, with `Lq` and `Lv` its partial
derivatives with respect to position and velocity.  Assume:

* `hinv`: `L` is invariant under translations `q ↦ q + a` (translation symmetry);
* `hLq`: `Lq q v` is the partial derivative of `L` in the position variable;
* `hEL`: along the trajectory `q` with velocity `v`, the Euler–Lagrange equation
  `d/dt (Lv (q t) (v t)) = Lq (q t) (v t)` holds.

Then the canonical momentum `p t = Lv (q t) (v t)` is conserved.
-/
