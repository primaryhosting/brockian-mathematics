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

@[simp] theorem upd_other (σ : Regs) (i j : ℕ) (v : Str) (h : j ≠ i) :
    upd σ i v j = σ j := by
  simp [upd, Function.update_of_ne h]

/-- Programs of the model.

* `pushBit i b` appends the bit `b` to register `i` (cost `1`);
* `tail i` drops the first bit of register `i` (cost `1`);
* `clear i` empties register `i` (cost `1`);
* `app i j` appends the contents of register `j` to register `i`
  (cost `1 + |reg j|`, i.e. one unit per copied bit);
* `query i j` queries the oracle on the contents of register `j` and stores the
  answer bit in register `i` (cost `1`);
* `guess i` appends a nondeterministically chosen bit to register `i` (cost `1`);
* `seq`, `whileNE i s` (loop while register `i` is nonempty) and
  `ifTrue i s t` (branch on whether register `i` starts with the bit `true`)
  are the usual control structures (cost `1` per test). -/
inductive Stmt : Type
  | noop : Stmt
  | pushBit (i : ℕ) (b : Bool) : Stmt
  | tail (i : ℕ) : Stmt
  | clear (i : ℕ) : Stmt
  | app (i j : ℕ) : Stmt
  | query (i j : ℕ) : Stmt
  | guess (i : ℕ) : Stmt
  | seq (s t : Stmt) : Stmt
  | whileNE (i : ℕ) (s : Stmt) : Stmt
  | ifTrue (i : ℕ) (s t : Stmt) : Stmt

deriving instance Countable for Stmt

instance : Inhabited Stmt := ⟨Stmt.clear 0⟩

/-- A program is deterministic when it contains no `guess`. -/
