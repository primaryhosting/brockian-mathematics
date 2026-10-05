/-
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Real

namespace Phys

/-- The spin-wave (harmonic) energy of the Fourier mode `j` of a nearest-neighbour
model on the `d`-dimensional discrete torus with `L` sites per side, in units where
the coupling constant is `1`.  The momentum attached to the mode `j` has components
`k i = 2π * j i / L`, and the lattice dispersion relation is
`ε k = ∑ i, 2 * (1 - cos (k i))`. -/

lemma sum_filter_tri (L : ℕ) [NeZero L] (F : (Fin 2 → Fin L) → ℝ) :
    ∑ j ∈ (Finset.univ.filter
        (fun j : Fin 2 → Fin L => 0 < (j 0 : ℕ) ∧ (j 0 : ℕ) ≤ (j 1 : ℕ))), F j
      = ∑ b : Fin L, ∑ a : Fin L, (if 0 < (a:ℕ) ∧ (a:ℕ) ≤ (b:ℕ) then F ![a, b] else 0) := by
  rw [Finset.sum_filter, ← Equiv.sum_comp (piFinTwoEquiv (fun _ => Fin L)).symm,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
  congr 1

/-- There are exactly `b` indices `a` with `0 < a ≤ b`. -/
