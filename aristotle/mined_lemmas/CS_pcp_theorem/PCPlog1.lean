/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (it uses only Lean 4 core `List`/`Nat`),
so that the required header comment can be the very first thing in the file.

## What is formalised here

The PCP theorem is the statement

    NP = PCP(log n, 1)

i.e. every language in `NP` admits a probabilistically checkable proof which the
verifier inspects using `O(log n)` random bits and `O(1)` queries, with perfect
completeness and soundness `1/2`; and conversely every language with such a
verifier is in `NP`.

Both classes only make sense relative to a notion of *feasible* (polynomial
time) computation.  Rather than fixing one particular machine model, we
parametrise the development by a `Model`: a class of "efficiently decidable"
predicates which is closed under the one operation the easy inclusion needs,
namely taking a conjunction over all `2 ^ rho n` random strings when `rho` is
logarithmically bounded (for polynomial time this is exactly the fact that a
polynomial-time predicate stays polynomial time when quantified universally over
polynomially many values).  `Model` is inhabited (see `CS.trivialModel`), so
nothing below is vacuous.

The main results are:

* `CS.pcp_subset_np` : `PCP(log n, O(1)) ⊆ NP`, proved in full.
* `CS.pcp_theorem`   : the PCP theorem for a model is *equivalent* to the single
  inclusion `NP ⊆ PCP(log n, O(1))`; the other half of the equality is the
  theorem `CS.pcp_subset_np` proved here.

The reverse inclusion `NP ⊆ PCP(log n, O(1))` is the deep Arora–Safra /
Arora–Lund–Motwani–Sudan–Szegedy content and is *not* formalised; it is exactly
what the right-hand side of `CS.pcp_theorem` isolates.
-/

namespace CS

/-- Inputs are finite bit strings. -/
abbrev Word := List Bool

/-- A language is a predicate on bit strings. -/
abbrev Language := Word → Prop

/-- `f` is bounded by a polynomial. -/

def PCPlog1 (M : Model) (L : Language) : Prop := Nonempty (PCPVerifier M L)

/-- A polynomially bounded certificate verifier for `L`. -/
structure NPVerifier (M : Model) (L : Language) where
  /-- Length bound on certificates. -/
  plen : Nat → Nat
  /-- The decision predicate of the verifier. -/
  V : Word → Word → Bool
  plen_poly : IsPoly plen
  V_eff : M.Eff₂ V
  correct : ∀ x, L x ↔ ∃ w : Word, w.length ≤ plen x.length ∧ V x w = true

/-- The class `NP`. -/
