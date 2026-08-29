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

theorem TM.toNTM_decidesInTime (M : TM) {L : Language} {f : Nat → Nat}
    (h : M.DecidesInTime L f) : M.toNTM.DecidesInTime L f := by
  intro w
  have ⟨t, ht, hhalt, hiff⟩ := h w
  constructor
  · intro hw
    have ⟨s, hs, hreach, _hrun⟩ := M.toNTM_reach_run w t
    exact ⟨s, Nat.le_trans hs ht, _, hreach, hiff.mpr hw⟩
  · intro hacc
    have ⟨s, hs, c, hreach, hc⟩ := hacc
    have hcs : c = M.run w s := by
      rw [M.toNTM_reach_eq hreach, M.run_eq_iter]
      rfl
    have hc' : (M.run w s).q = M.acc := hcs ▸ hc
    have hhalt' : M.Halted (M.run w s) := Or.inl hc'
    cases Nat.le_total s t with
    | inl hst =>
      have heq : M.run w t = M.run w s := M.run_eq_of_halted hhalt' hst
      exact hiff.mp (by rw [heq]; exact hc')
    | inr hts =>
      have heq : M.run w s = M.run w t := M.run_eq_of_halted hhalt hts
      exact hiff.mp (by rw [← heq]; exact hc')

/-! ## `P ⊆ NP` -/

/-- Every language decidable in deterministic polynomial time is decidable in
nondeterministic polynomial time. -/
