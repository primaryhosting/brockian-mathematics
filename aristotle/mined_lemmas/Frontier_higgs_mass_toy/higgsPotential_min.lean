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


theorem higgsPotential_min {lam : Rat} (hlam : 0 ≤ lam) (v r : Rat) :
    higgsPotential lam v v ≤ higgsPotential lam v r := by
  have h0 : higgsPotential lam v v = 0 := by grind [higgsPotential]
  have h1 : 0 ≤ lam * (r ^ 2 - v ^ 2) ^ 2 :=
    Rat.mul_nonneg hlam (sq_nonneg_rat _)
  grind [higgsPotential]

/-- Exact expansion of the potential around the vacuum `r = v + h`.  There is no
term linear in `h` (so `v` is a stationary point), and the quadratic coefficient is
`(1/2) * V''(v) = 4 * lam * v ^ 2 = (1/2) * higgsMassSq lam v`. -/
