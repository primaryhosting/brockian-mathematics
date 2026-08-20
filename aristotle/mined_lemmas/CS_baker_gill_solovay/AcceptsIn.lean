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

def AcceptsIn (O : Oracle) (s : Stmt) (t : ℕ) (x : Str) : Prop :=
  ∃ σ' c tr, Exec O s (init x) σ' c tr ∧ c ≤ t ∧ Acc σ'

/-- The class `NP^O`. -/
