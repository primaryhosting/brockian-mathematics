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

def AdmissibleAt (H : List Int) (p : Nat) : Prop :=
  ∃ r : Int, 0 ≤ r ∧ r < (p : Int) ∧ ∀ h ∈ H, h % (p : Int) ≠ r

/-- A tuple of integers is *admissible* in the sense of the Hardy–Littlewood prime `k`-tuples
conjecture if, for every prime `p`, its reductions modulo `p` do not cover all residue classes.
This is exactly the condition under which the associated singular series `𝔖(H)` is nonzero. -/
