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


theorem mul_self_pos_rat {x : Rat} (hx : x ≠ 0) : 0 < x * x := by
  rcases (Rat.le_total (a := 0) (b := x)) with h | h
  · have hx' : 0 < x := by grind
    exact Rat.mul_pos hx' hx'
  · have h' : 0 < -x := by grind
    have := Rat.mul_pos h' h'
    grind

