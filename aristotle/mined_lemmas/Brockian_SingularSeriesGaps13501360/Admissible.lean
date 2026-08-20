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

def Admissible (H : List Int) : Prop :=
  ∀ p : Nat, NatPrime p → AdmissibleAt H p

/-- A gap pair `{0, h}` with `h` even is admissible: modulo `2` both entries are `≡ 0`, and modulo
any prime `p ≥ 3` the two entries cannot cover the three residues `0, 1, 2`. -/
