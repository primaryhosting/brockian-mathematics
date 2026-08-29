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


theorem sq_pos_rat {x : Rat} (hx : x ≠ 0) : 0 < x ^ 2 := by
  have := mul_self_pos_rat hx
  grind

/-! ### The abelian Higgs toy model -/

/-- The "Mexican hat" scalar potential of the abelian Higgs toy model, written as a
function of the modulus `r = |φ|` of the complex scalar field:
`V(r) = lam * (r ^ 2 - v ^ 2) ^ 2`.
Its minima form the circle `|φ| = v`: choosing one of them is the spontaneous
breaking of the `U(1)` gauge symmetry. -/
