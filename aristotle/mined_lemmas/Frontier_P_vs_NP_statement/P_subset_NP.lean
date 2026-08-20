/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
/-!
## Overview

This file is a self-contained formalisation (it needs no imports beyond the Lean core
prelude, so that the module header above can literally begin the file) of:

* single-tape Turing machines over the binary alphabet, deterministic (`Frontier.DTM`) and
  nondeterministic (`Frontier.NTM`), with a *finite* state set `Fin (states + 1)`;
* their step semantics on a two-way infinite tape `Int → Sym`;
* time-bounded decision of a language, and the complexity classes `Frontier.P` and
  `Frontier.NP`;
* polynomial-time computable functions, Karp (polynomial-time many-one) reducibility
  `Frontier.PolyReducible`, NP-hardness and NP-completeness.

The target declaration `Frontier.P_vs_NP_statement` states the precise content of the
assertion `P ≠ NP`: the classes differ exactly when some language is decided by a
polynomial-time nondeterministic Turing machine but by no polynomial-time deterministic one.
The theorem is the conjunction of the (proved) inclusion `P ⊆ NP` with pure logic; the
assertion `P ≠ NP` itself is of course open, and is *not* proved here.
-/

namespace Frontier

/-! ## Words, languages, tapes -/

/-- The tape alphabet: `none` is the blank symbol, `some b` is the bit `b`. -/
abbrev Sym : Type := Option Bool

/-- A word is a finite binary string. -/
abbrev Word : Type := List Bool

/-- A language is a set of binary words. -/
abbrev Language : Type := Word → Prop

/-- The initial tape holding the input word `x`: the `i`-th cell (for `i ≥ 0`) holds the
`i`-th bit of `x`, and all other cells are blank. -/

theorem P_subset_NP : ∀ L : Language, P L → NP L := by
  intro L hL
  match hL with
  | ⟨D, f, hf, hdec⟩ =>
    refine ⟨D.toNTM, f, hf, ?_⟩
    intro x
    match hdec x with
    | ⟨t, ht, c, hrun, hhalt, hacc⟩ =>
      constructor
      · intro hx
        exact ⟨t, ht, c, DTM.toNTM_reaches.2 hrun, DTM.toNTM_halt.2 hhalt, hacc.2 hx⟩
      · intro hx
        match hx with
        | ⟨s, _, c', hreach, hhalt', hacc'⟩ =>
          have h1 : D.run s (initCfg D.states x) = some c' := DTM.toNTM_reaches.1 hreach
          have h2 : D.step c' = none := DTM.toNTM_halt.1 hhalt'
          have hc : c' = c := D.halt_unique h1 h2 hrun hhalt
          exact hacc.1 (hc ▸ hacc')

/-! ## Sanity checks: the classes are non-vacuous -/

/-- The machine with a single state that halts immediately; it accepts iff `b` holds. -/
