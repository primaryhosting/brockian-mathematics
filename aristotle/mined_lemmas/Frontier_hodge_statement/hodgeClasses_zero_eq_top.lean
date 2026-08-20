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

lemma hodgeClasses_zero_eq_top (H : HodgeStructure V (2 * 0)) :
    hodgeClasses 0 H = ⊤ := by
  simp [hodgeClasses, H.piece_zero_eq_top]

/-! ## The cohomological data of a smooth projective complex variety -/

/-- The data entering the Hodge conjecture for a smooth **connected** projective complex
variety `X`:

* `H p` is the rational cohomology `H^{2p}(X, ℚ)`, carrying a rational Hodge structure of
  weight `2p`;
* `Cyc p` is the `ℚ`-vector space of algebraic cycles of codimension `p` on `X` with
  rational coefficients, and `cl p` is the cycle class map;
* `cl_hodge` records the classical fact that cycle classes are Hodge classes;
* `fund` is the fundamental class `[X] ∈ Cyc 0`, whose image spans `H^0(X, ℚ)` because
  `X` is connected.

Since Mathlib has neither singular cohomology of complex varieties nor Chow groups, this
structure axiomatises exactly the input needed to state the conjecture. -/
structure HodgeData where
  /-- The rational cohomology group `H^{2p}(X, ℚ)`. -/
  H : ℕ → Type*
  [addCommGroupH : ∀ p, AddCommGroup (H p)]
  [moduleH : ∀ p, Module ℚ (H p)]
  /-- The Hodge structure of weight `2p` on `H^{2p}(X, ℚ)`. -/
  hs : ∀ p, HodgeStructure (H p) (2 * p)
  /-- Codimension-`p` algebraic cycles with rational coefficients. -/
  Cyc : ℕ → Type*
  [addCommGroupCyc : ∀ p, AddCommGroup (Cyc p)]
  [moduleCyc : ∀ p, Module ℚ (Cyc p)]
  /-- The cycle class map. -/
  cl : ∀ p, Cyc p →ₗ[ℚ] H p
  /-- Cycle classes are Hodge classes. -/
  cl_hodge : ∀ p, LinearMap.range (cl p) ≤ hodgeClasses p (hs p)
  /-- The fundamental class of `X`. -/
  fund : Cyc 0
  /-- `X` is connected: `H^0(X, ℚ)` is spanned by the fundamental class. -/
  connected : Submodule.span ℚ {cl 0 fund} = ⊤

attribute [instance] HodgeData.addCommGroupH HodgeData.moduleH
attribute [instance] HodgeData.addCommGroupCyc HodgeData.moduleCyc

/-- The Hodge conjecture in codimension `p`: every Hodge class of type `(p,p)` on `X` is a
rational linear combination of classes of algebraic cycles, i.e. the image of the cycle
class map is exactly the space of Hodge classes. -/
