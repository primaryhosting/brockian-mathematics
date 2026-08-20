/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: the requested header is reproduced verbatim above, but as an ordinary block comment
`/- ... -/` rather than a module docstring `/-! ... -/`, since Lean 4 does not allow a module
docstring to precede the `import` commands.)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- A finite set of nonnegative integers `H` (a *gap range*, or prime tuple pattern) is
*admissible* when, for every prime `p`, the reductions of the elements of `H` modulo `p`
do not cover all of `ZMod p`.  Equivalently the local factor
`1 - ν_H(p)/p` of the Hardy–Littlewood singular series is strictly positive at every prime,
which is exactly the condition for the singular series `𝔖(H)` to be nonzero. -/

theorem admissibleTuple_image_add_iff (H : Finset ℕ) (c : ℕ) :
    AdmissibleTuple (H.image (fun h => h + c)) ↔ AdmissibleTuple H := by
  constructor
  · intro hH p hp
    obtain ⟨r, hr⟩ := hH p hp
    refine ⟨r - (c : ZMod p), ?_⟩
    intro h hh hcon
    refine hr (h + c) (Finset.mem_image.mpr ⟨h, hh, rfl⟩) ?_
    push_cast
    rw [hcon]
    ring
  · intro hH p hp
    obtain ⟨r, hr⟩ := hH p hp
    refine ⟨r + (c : ZMod p), ?_⟩
    intro h hh hcon
    obtain ⟨h₀, hh₀, rfl⟩ := Finset.mem_image.mp hh
    refine hr h₀ hh₀ ?_
    push_cast at hcon
    exact add_right_cancel hcon

/-- A concrete new admissible gap range of length 7 coming from the prime block
`{11, 13, 17, 19, 23, 29, 31}`. -/
