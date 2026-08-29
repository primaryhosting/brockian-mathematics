/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
A self-contained formalization of the P vs NP question in terms of time-bounded
(deterministic and nondeterministic) single-tape Turing machines and polynomial-time
many-one reducibility.

The development is elementary and depends on nothing beyond the Lean 4 prelude, so that
the file can literally begin with the header comment above.

Main declarations:

* `Frontier.Machine`             : single-tape Turing machine with finite control;
* `Frontier.AcceptsWithin`       : acceptance within a given number of steps;
* `Frontier.Deterministic`       : determinism of the transition relation;
* `Frontier.DecidesInPolyTime`   : deciding a language within a polynomial time bound;
* `Frontier.P`, `Frontier.NP`    : the two complexity classes;
* `Frontier.PolyReducible`       : polynomial-time many-one reducibility `≤ₚ`;
* `Frontier.NPComplete`          : NP-completeness;
* `Frontier.P_vs_NP_statement`   : the statement of the P vs NP problem, in the form
  `P ≠ NP ↔ ∃ L, L ∈ NP ∧ L ∉ P`.
-/

namespace Frontier

/-- Words are finite binary strings. -/
abbrev Word : Type := List Bool

/-- A language is a set of words, represented by its membership predicate. -/
abbrev Language : Type := Word → Prop

/-- The direction in which the tape head moves in one step. -/
inductive Dir : Type
  | left : Dir
  | right : Dir
  | stay : Dir

/-- The displacement of the head associated with a direction. -/

def Deterministic (M : Machine) : Prop :=
  ∀ (q : M.State) (a : Option Bool) (q₁ : M.State) (w₁ : Option Bool) (d₁ : Dir)
    (q₂ : M.State) (w₂ : Option Bool) (d₂ : Dir),
    M.next q a q₁ w₁ d₁ → M.next q a q₂ w₂ d₂ → q₁ = q₂ ∧ w₁ = w₂ ∧ d₁ = d₂

/-- `M` decides `L` in polynomial time: there are constants `c, k` such that a word `x`
belongs to `L` exactly when `M` accepts `x` within `c * |x| ^ k + c` steps. -/
