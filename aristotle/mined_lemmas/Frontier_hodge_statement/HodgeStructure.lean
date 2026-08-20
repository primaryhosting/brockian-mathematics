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

lemma HodgeStructure.piece_zero_eq_top (H : HodgeStructure V (2 * 0)) :
    H.piece (0, 0) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← H.internal.submodule_iSup_eq_top]
  refine iSup_le fun pq => ?_
  rcases eq_or_ne (pq.1 + pq.2) (2 * 0) with h | h
  · have h1 : pq.1 = 0 := by omega
    have h2 : pq.2 = 0 := by omega
    have : pq = (0, 0) := Prod.ext h1 h2
    exact this ▸ le_rfl
  · exact (H.weight pq h).le.trans bot_le

/-- Every rational class is a Hodge class in weight `0`. -/
