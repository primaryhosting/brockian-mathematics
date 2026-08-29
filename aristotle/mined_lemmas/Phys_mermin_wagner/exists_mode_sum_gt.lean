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

lemma exists_mode_sum_gt (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ 2) (B : ℝ) :
    ∃ (L : ℕ) (D : Finset (Fin d → Fin L)),
      (∀ j ∈ D, ∃ i, (j i : ℕ) ≠ 0) ∧
      B * (L : ℝ) ^ d < ∑ j ∈ D, 1 / modeSq d L j := by
  interval_cases d
  · exact exists_mode_sum_gt_one B
  · exact exists_mode_sum_gt_two B

/--
**Mermin–Wagner theorem.**

There is no spontaneous breaking of a continuous symmetry at positive temperature in
dimension `d ≤ 2`.

The setting is a nearest-neighbour spin model with a continuous internal symmetry on
the `d`-dimensional discrete torus with `L` sites per side, at temperature `T > 0`.
`S L j` denotes the static structure factor (the thermal expectation `⟨|S k|²⟩` of the
squared transverse spin fluctuation) of the Fourier mode `j`, and `m` denotes the
spontaneous magnetisation of the symmetry-breaking order parameter.  The two physical
inputs are:

* the *sum rule* `∑ k, ⟨|S k|²⟩ ≤ L ^ d`, expressing that the spins have bounded
  length (normalised to `1`);
* the *Bogoliubov inequality* `T * m² ≤ 2 * C * ε k * ⟨|S k|²⟩` for every nonzero mode
  `k`, where `ε k` is the spin-wave energy and `C > 0` is a constant built from the
  interaction strength.

The conclusion is that the magnetisation vanishes, `m = 0`: the continuous symmetry
cannot be spontaneously broken.  The mechanism is the infrared divergence of
`∑_{k ≠ 0} |k|⁻²` relative to the volume in dimensions `d ≤ 2`.
-/
