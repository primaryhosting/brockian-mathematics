/-!
# Higgs Mass Toy
Category: Frontier Physics
Target: Frontier.higgs_mass_toy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (Lean core only), so that the header comment
above is literally the first thing in the file.  All arithmetic therefore takes
place in the rational numbers `Rat` of Lean core.  A companion file
`RequestProject/HiggsMassToyReal.lean` develops the same toy model over the real
numbers with genuine derivatives (`Frontier.higgs_mass_toy_real`).
-/

namespace Frontier

/-! ### Auxiliary order facts for `Rat` (core only) -/


theorem higgsPotential_expansion (lam v h : Rat) :
    higgsPotential lam v (v + h)
      = (1 / 2) * higgsMassSq lam v * h ^ 2 + 4 * lam * v * h ^ 3 + lam * h ^ 4 := by
  unfold higgsPotential higgsMassSq
  grind

/--
**Abelian Higgs toy model: spontaneous symmetry breaking gives the gauge boson a mass.**

Assume a strictly positive quartic coupling `lam`, a nonzero gauge coupling `g`, and a
nonzero vacuum expectation value `v` (the spontaneously broken phase).  Then:

1. the vacuum `|φ| = v` has zero potential energy and is a global minimum of the
   Mexican-hat potential;
2. expanding around the vacuum, `V(v + h)` has no linear term and quadratic
   coefficient `(1/2) * higgsMassSq lam v`, i.e. the radial excitation has mass
   squared `V''(v) = 8 * lam * v ^ 2`, which is strictly positive;
3. the gauge boson acquires a strictly positive mass squared
   `gaugeMassSq g v = g ^ 2 * v ^ 2 = (g * v) ^ 2 > 0`;
4. by contrast, in the unbroken phase `v = 0` the gauge boson stays exactly massless
   and the radial mode is massless as well.
-/
