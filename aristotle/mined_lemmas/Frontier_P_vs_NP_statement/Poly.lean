/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses only the Lean 4 core library),
so that the formal statement of the P vs NP problem depends on as little as possible.

We define:
* single-tape deterministic Turing machines and their step-by-step semantics;
* single-tape nondeterministic Turing machines and their reachability semantics;
* the classes `Frontier.P` and `Frontier.NP` of languages decidable in polynomial time by
  deterministic resp. nondeterministic machines;
* polynomial-time computable functions, polynomial-time many-one reducibility `≤p`,
  NP-hardness and NP-completeness;
* the proposition `Frontier.PNeqNP`, i.e. `P ≠ NP`.

The main theorem `Frontier.P_vs_NP_statement` records the precise statement together with
its standard reformulation: `P ≠ NP` holds if and only if some language is decidable in
nondeterministic polynomial time but not in deterministic polynomial time.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Frontier

/-! ## Words and languages -/

/-- Inputs are finite binary strings. -/
abbrev Word : Type := List Bool

/-- The tape alphabet: `none` is the blank symbol, `some b` a binary symbol. -/
abbrev Sym : Type := Option Bool

/-- A language is a set of binary strings, represented by its characteristic predicate. -/
abbrev Language : Type := Word → Prop

/-- Head movement directions. -/
inductive Dir : Type
  | left : Dir
  | right : Dir
  | stay : Dir
  deriving DecidableEq

/-- Moving the head position according to a direction. -/

def Poly (f : Nat → Nat) : Prop := ∃ c k : Nat, ∀ n : Nat, f n ≤ c * (n + 1) ^ k

/-- `M` decides the language `L` within time `f`: on every input `w`, within `f |w|`
steps the machine halts, and it halts in the accepting state exactly when `w ∈ L`. -/
