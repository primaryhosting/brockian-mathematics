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

def AdmissibleAtZMod (H : Finset ℤ) (p : ℕ) : Prop :=
  ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- A finite set of integers is admissible (Hardy–Littlewood prime tuples): for every prime `p`
its reductions modulo `p` do not cover all of `ZMod p`.  This is equivalent to non-vanishing of
the singular series `𝔖(H)`. -/
