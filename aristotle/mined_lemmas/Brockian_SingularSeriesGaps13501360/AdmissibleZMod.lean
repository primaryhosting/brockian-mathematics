import Mathlib

/-!
# Singular Series Gaps 13501360 — `ZMod`/Mathlib formulation

Companion to `RequestProject/SingularSeriesGaps13501360.lean`.  The target file there is stated
with elementary `Int` arithmetic (it must begin with a fixed header comment, which precludes an
`import` line); here the same mathematics is recorded in the idiomatic Mathlib language of
`Finset ℤ` and `ZMod p`.
-/

namespace Brockian

/-- A finite set of integers misses a residue class modulo `p`. -/

def AdmissibleZMod (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → AdmissibleAtZMod H p

/-- If `H` has fewer than `p` elements, its reductions cannot cover all `p` residues mod `p`. -/
