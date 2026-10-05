/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-! ## Tape alphabet, configurations and machines -/

/-- The tape alphabet: `none` is the blank symbol, `some b` a bit. -/
abbrev Alpha := Option Bool

/-- A language: a set of finite bit strings, presented as a predicate. -/
abbrev Language := List Bool → Prop

/-- A configuration of a one-tape Turing machine with state space `Λ`:
the current state, the (two-way infinite) tape contents and the head position. -/
structure Cfg (Λ : Type) where
  state : Λ
  tape : Int → Alpha
  pos : Int

/-- A (in general nondeterministic) one-tape Turing machine with state space `Λ`.
`δ q a (q', a', d)` holds when, reading the symbol `a` in state `q`, the machine may move
to state `q'`, write `a'` and move right (`d = true`) or left (`d = false`).
A state/symbol pair with no transition is a halting situation. -/
structure NTM (Λ : Type) where
  /-- the initial state -/
  start : Λ
  /-- the accepting states -/
  accept : Λ → Prop
  /-- the transition relation -/
  δ : Λ → Alpha → (Λ × Alpha × Bool) → Prop

variable {Λ : Type}

/-- The machine is deterministic: at most one transition per (state, symbol) pair. -/

theorem halted_unique {M : NTM Λ} (hM : M.Deterministic) :
    ∀ (k k' : Nat) (c₀ c c' : Cfg Λ), StepN M k c₀ c → Halted M c →
      StepN M k' c₀ c' → Halted M c' → c = c' := by
  intro k
  induction k with
  | zero =>
      intro k' c₀ c c' h hc h' hc'
      cases h
      cases k' with
      | zero => cases h'; rfl
      | succ j =>
          obtain ⟨c₁, hstep, -⟩ := h'
          exact absurd hstep (halted_not_step hc)
  | succ i ih =>
      intro k' c₀ c c' h hc h' hc'
      obtain ⟨c₁, hstep, hrest⟩ := h
      cases k' with
      | zero =>
          cases h'
          exact absurd hstep (halted_not_step hc')
      | succ j =>
          obtain ⟨c₂, hstep', hrest'⟩ := h'
          have hc₁ : c₁ = c₂ := step_det hM hstep hstep'
          subst hc₁
          exact ih j c₁ c c' hrest hc hrest' hc'

/-- Every language in `P` lies in `NP`: a deterministic machine is in particular a
nondeterministic one, and by uniqueness of its halting configuration it accepts exactly the
strings of the language it decides. -/
