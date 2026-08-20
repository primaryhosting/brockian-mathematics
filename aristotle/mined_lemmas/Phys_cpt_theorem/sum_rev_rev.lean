/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Matrix

namespace Phys

/-! ## Complexified Minkowski space and the complex Lorentz group -/

/-- Real Minkowski space `ℝ^{1,3}`. -/
abbrev Spacetime := Fin 4 → ℝ

/-- Complexified Minkowski space `ℂ^4`, the domain of the analytically continued
Wightman functions. -/
abbrev CSpace := Fin 4 → ℂ

/-- The Minkowski bilinear form on real Minkowski space (signature `+ - - -`). -/

private lemma sum_rev_rev {n : ℕ} (f : Fin n → Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n, f (Fin.rev i) (Fin.rev j)) = ∑ i, ∑ j, f i j :=
  calc (∑ i : Fin n, ∑ j : Fin n, f (Fin.rev i) (Fin.rev j))
      = ∑ i : Fin n, ∑ j : Fin n, f (Fin.rev i) j :=
        Finset.sum_congr rfl fun i _ => Equiv.sum_comp Fin.revPerm fun j => f (Fin.rev i) j
    _ = ∑ i, ∑ j, f i j := Equiv.sum_comp Fin.revPerm fun i => ∑ j, f i j

/-- A concrete, nonzero example of a structure satisfying all the Wightman axioms used
above, showing that the hypotheses of `cpt_theorem` are not vacuous. -/
