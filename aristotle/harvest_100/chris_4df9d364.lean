import Mathlib

/-!
# Complement closure for regular languages, in Mathlib's language

This file restates `CS.dfa_complement_regular` using Mathlib's `Language.IsRegular`
(defined via `DFA`s with a `Fintype` of states).
-/

universe u

namespace CS

/--
**Regular languages are closed under complement**, phrased with Mathlib's `Language.IsRegular`.

The proof is the standard DFA construction: keep the states, the start state and the transition
function of a DFA recognizing `L`, and complement its set of accepting states.

Mathlib also has this result, as `Language.IsRegular.compl` / `Language.IsRegular_compl`.
-/
theorem dfa_complement_regular_language {T : Type u} {L : Language T} (h : L.IsRegular) :
    Lᶜ.IsRegular := by
  obtain ⟨σ, hσ, M, hM⟩ := h
  -- `Mᶜ` is by definition `⟨M.step, M.start, M.acceptᶜ⟩` (`DFA.compl_def`).
  refine ⟨σ, hσ, Mᶜ, ?_⟩
  rw [DFA.accepts_compl, hM]

end CS

/-!
# Dfa Complement Regular
Category: Computer Science
Target: CS.dfa_complement_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (Lean requires `import` commands to precede any
module documentation, and the header above must be the very first thing in the file), so the
development below is self-contained: deterministic finite automata, the languages they accept,
regularity, and closure of the regular languages under complement.

A Mathlib-based version of the same statement, phrased with `Language.IsRegular`, is proved in
`RequestProject/MathlibVersion.lean` (`CS.dfa_complement_regular_language`).
-/

namespace CS

universe u v

/-- A deterministic finite automaton over the input alphabet `α` with state type `σ`:
a transition function, an initial state, and a set of accepting states. -/
structure DFA (α : Type u) (σ : Type v) where
  /-- The transition function. -/
  step : σ → α → σ
  /-- The initial state. -/
  start : σ
  /-- The set of accepting states. -/
  accept : σ → Prop

namespace DFA

variable {α : Type u} {σ : Type v}

/-- Run the automaton on a word, starting from the state `s`. -/
def evalFrom (M : DFA α σ) : σ → List α → σ
  | s, [] => s
  | s, a :: w => M.evalFrom (M.step s a) w

/-- Run the automaton on a word, starting from its initial state. -/
def eval (M : DFA α σ) (w : List α) : σ := M.evalFrom M.start w

/-- The language accepted by the automaton: the words whose run ends in an accepting state. -/
def accepts (M : DFA α σ) (w : List α) : Prop := M.accept (M.eval w)

end DFA

/-- A language over the alphabet `α`, viewed as a predicate on words. -/
def Lang (α : Type u) : Type u := List α → Prop

/-- A language is regular when some DFA with finitely many states accepts exactly it. -/
def IsRegular {α : Type u} (L : Lang α) : Prop :=
  ∃ n : Nat, ∃ M : DFA α (Fin n), ∀ w, M.accepts w ↔ L w

/-- The complement of a language. -/
def Lang.compl {α : Type u} (L : Lang α) : Lang α := fun w => ¬ L w

/--
**Regular languages are closed under complement.**

Given a DFA `M` recognizing `L`, the DFA with the same states, initial state and transition
function, but with the complemented set of accepting states, recognizes the complement of `L`.
-/
theorem dfa_complement_regular {α : Type u} {L : Lang α} (h : IsRegular L) :
    IsRegular L.compl := by
  obtain ⟨n, M, hM⟩ := h
  refine ⟨n, ⟨M.step, M.start, fun s => ¬ M.accept s⟩, fun w => ?_⟩
  have hstep : ∀ (s : Fin n) (w : List α),
      DFA.evalFrom ⟨M.step, M.start, fun s => ¬ M.accept s⟩ s w = M.evalFrom s w := by
    intro s w
    induction w generalizing s with
    | nil => rfl
    | cons a w ih => simpa [DFA.evalFrom] using ih (M.step s a)
  show ¬ M.accept (DFA.evalFrom ⟨M.step, M.start, fun s => ¬ M.accept s⟩ M.start w) ↔ ¬ L w
  rw [hstep]
  exact not_congr (hM w)

end CS

