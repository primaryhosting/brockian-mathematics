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

lemma modeSq_pos {d L : ℕ} {j : Fin d → Fin L} (hj : ∃ i, (j i : ℕ) ≠ 0) :
    0 < modeSq d L j := by
  obtain ⟨i, hi⟩ := hj
  have hL : (0:ℝ) < (L:ℝ) := by exact_mod_cast (j i).pos
  have h1 : (0:ℝ) < ((j i : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hi
  refine Finset.sum_pos' (fun k _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  positivity

/-- In one dimension the sum `∑_{k ≠ 0} |k|⁻²` over the Brillouin zone grows faster
than the volume `L`. -/
