/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Real
open Finset

namespace Frontier

/-- The representative of an angle `x` modulo `2π` obtained by subtracting the nearest
multiple of `2π`.  This is the "principal branch" of the logarithm of `exp (i x)`. -/

lemma sum_plaquette_raw [NeZero N] [NeZero M] (A1 A2 : ZMod N × ZMod M → ℝ) :
    ∑ k : ZMod N × ZMod M,
      (A1 k + A2 (k.1 + 1, k.2) - A1 (k.1, k.2 + 1) - A2 k) = 0 := by
  have h1 : ∑ k : ZMod N × ZMod M, A1 (k.1, k.2 + 1) = ∑ k : ZMod N × ZMod M, A1 k := by
    refine Fintype.sum_equiv
      ((Equiv.refl (ZMod N)).prodCongr (Equiv.addRight (1 : ZMod M))) _ _ ?_
    intro k
    rfl
  have h2 : ∑ k : ZMod N × ZMod M, A2 (k.1 + 1, k.2) = ∑ k : ZMod N × ZMod M, A2 k := by
    refine Fintype.sum_equiv
      ((Equiv.addRight (1 : ZMod N)).prodCongr (Equiv.refl (ZMod M))) _ _ ?_
    intro k
    rfl
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2]
  ring

/-- **Integrality of the lattice Chern number.**  The total Berry curvature over the
Brillouin torus is an integer multiple of `2π`. -/
