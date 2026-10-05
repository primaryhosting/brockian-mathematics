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

theorem polyComputable_id : PolyComputable (fun w : Word => w) := by
  refine ⟨idTM, fun _ => 0, ⟨0, 0, fun n => Nat.zero_le _⟩, ?_⟩
  intro w
  refine ⟨0, Nat.le_refl 0, Or.inl rfl, ?_, ?_⟩
  · intro i hi
    show initTape w (i : Int) = _
    unfold initTape
    rw [if_pos (by omega : (0 : Int) ≤ (i : Int))]
    have : ((i : Int)).toNat = i := by omega
    rw [this]
  · show initTape w (w.length : Int) = none
    unfold initTape
    rw [if_pos (by omega : (0 : Int) ≤ (w.length : Int))]
    have : ((w.length : Int)).toNat = w.length := by omega
    rw [this]
    exact List.getElem?_eq_none (Nat.le_refl _)

/-- The machine that immediately halts in its rejecting state (which is distinct from its
accepting state). -/
