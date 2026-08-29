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

theorem P_ne_NP_of_NPComplete_not_mem_P (L : Language) (hL : NPComplete L) (hP : ¬ P L) :
    P ≠ NP := fun h => hP (NPComplete_mem_P_of_P_eq_NP L h hL)

/-! ### The statement of the P vs NP problem -/

/-- **The P vs NP question.**

With `P` and `NP` defined through polynomial-time bounded deterministic and
nondeterministic single-tape Turing machines as above, the assertion `P ≠ NP` says
precisely that some language is decidable in nondeterministic polynomial time but not in
deterministic polynomial time.

(The separation itself is a famous open problem and is *not* proved here: what is proved
is that the formal statement `P ≠ NP` is equivalent to the existence of such a language,
which uses the inclusion `P ⊆ NP`.) -/
