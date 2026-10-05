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

lemma sum_ite_Ioc (L : ℕ) [NeZero L] (b : Fin L) (c : ℝ) :
    ∑ a : Fin L, (if 0 < (a:ℕ) ∧ (a:ℕ) ≤ (b:ℕ) then c else 0) = (b:ℕ) * c := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero]
  have h : (Finset.univ.filter (fun a : Fin L => 0 < (a:ℕ) ∧ (a:ℕ) ≤ (b:ℕ)))
      = Finset.Ioc 0 b := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioc,
      Fin.lt_def, Fin.le_def, Fin.val_zero]
  rw [h, Fin.card_Ioc]
  simp

/-- In two dimensions the sum `∑_{k ≠ 0} |k|⁻²` over the Brillouin zone grows faster
than the volume `L²`: this is the logarithmic infrared divergence responsible for the
Mermin–Wagner theorem in the critical dimension. -/
