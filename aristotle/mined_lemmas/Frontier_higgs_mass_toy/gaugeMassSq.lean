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


def gaugeMassSq (g v : Rat) : Rat := g ^ 2 * v ^ 2

/-- The mass squared of the radial (Higgs) excitation, i.e. the curvature
`V''(v)` of the potential at the vacuum. -/
