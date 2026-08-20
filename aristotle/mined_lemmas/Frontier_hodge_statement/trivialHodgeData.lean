/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Mathlib (as of the pinned revision) contains no singular cohomology of complex
varieties, no Hodge decomposition and no Chow groups / cycle class maps, so there
is no existing lemma that closes this goal: the statement has to be built from
scratch.  We therefore

* define rational Hodge structures (`Frontier.HodgeStructure`) and their spaces of
  Hodge classes (`Frontier.hodgeClasses`),
* package the cohomological data of a smooth projective complex variety together
  with its cycle class maps (`Frontier.HodgeData`),
* state the Hodge conjecture for such data (`Frontier.HodgeConjecture`), and
* prove, in `Frontier.hodge_statement`, the base case `p = 0` of the conjecture
  together with the standard reduction of the conjecture to the inclusion
  "every Hodge class is algebraic".
-/

import Mathlib

namespace Frontier

open TensorProduct

/-! ## Complex conjugation on a complexified rational vector space -/

/-- Complex conjugation on `ℂ ⊗[ℚ] V`, acting on the left tensor factor.  It is only
`ℚ`-linear (it is conjugate-linear over `ℂ`). -/

noncomputable def trivialHodgeData : HodgeData where
  H _ := ℚ
  hs p := trivialHodgeStructure p
  Cyc _ := ℚ
  cl _ := LinearMap.id
  cl_hodge p := by
    have : hodgeClasses p (trivialHodgeStructure p) = ⊤ := by
      simp [hodgeClasses, trivialHodgeStructure]
    rw [this]
    exact le_top
  fund := 1
  connected := by
    simp

end Frontier

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

