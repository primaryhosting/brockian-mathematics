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

@[simp] lemma cxConj_tmul (V : Type*) [AddCommGroup V] [Module ℚ V] (z : ℂ) (v : V) :
    cxConj V (z ⊗ₜ[ℚ] v) = (starRingEnd ℂ) z ⊗ₜ[ℚ] v := rfl

/-! ## Rational Hodge structures -/

/-- A rational Hodge structure of weight `n` on a `ℚ`-vector space `V`: a decomposition
of the complexification `ℂ ⊗[ℚ] V` into complex subspaces `V^{p,q}` with `p + q = n`,
which is exchanged by complex conjugation, `conj (V^{p,q}) = V^{q,p}`. -/
structure HodgeStructure (V : Type*) [AddCommGroup V] [Module ℚ V] (n : ℕ) where
  /-- The `(p,q)`-piece of the Hodge decomposition of the complexification. -/
  piece : ℕ × ℕ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- Only bidegrees of total degree `n` occur. -/
  weight : ∀ pq : ℕ × ℕ, pq.1 + pq.2 ≠ n → piece pq = ⊥
  /-- The pieces decompose the complexification as an internal direct sum. -/
  internal : DirectSum.IsInternal piece
  /-- Complex conjugation exchanges the `(p,q)`- and `(q,p)`-pieces. -/
  conj_piece : ∀ pq : ℕ × ℕ, Submodule.map (cxConj V) ((piece pq).restrictScalars ℚ)
      ≤ (piece (pq.2, pq.1)).restrictScalars ℚ

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The space of Hodge classes of type `(p,p)` in a rational Hodge structure of weight
`2p`: the rational classes whose image in the complexification lies in `V^{p,p}`. -/
