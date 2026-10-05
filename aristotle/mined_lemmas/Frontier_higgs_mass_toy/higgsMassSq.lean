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


def higgsMassSq (lam v : Rat) : Rat := 8 * lam * v ^ 2

/-- The vacuum `r = v` is a global minimum of the Mexican-hat potential. -/
