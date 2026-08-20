import Mathlib

/-!
# A model of relativized (oracle) polynomial-time computation

We fix a small imperative programming language over string-valued registers,
with an oracle-query primitive and a nondeterministic guess primitive, and an
explicit step-cost semantics.  This is the machine model used to define the
relativized classes `P^O` and `NP^O`.
-/

namespace BGS

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a set of strings (given as a predicate). -/
abbrev Oracle := Str → Prop

/-- A register file: countably many string-valued registers. -/
abbrev Regs := ℕ → Str

/-- Update a register. -/

@[simp] theorem upd_self (σ : Regs) (i : ℕ) (v : Str) : upd σ i v i = v := by
  simp [upd]

