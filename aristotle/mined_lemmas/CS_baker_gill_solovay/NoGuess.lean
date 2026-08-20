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

def NoGuess : Stmt → Prop
  | .guess _ => False
  | .seq s t => NoGuess s ∧ NoGuess t
  | .whileNE _ s => NoGuess s
  | .ifTrue _ s t => NoGuess s ∧ NoGuess t
  | _ => True

/-- Big-step semantics: `Exec O s σ σ' c tr` says that, with oracle `O`, the
program `s` started in register file `σ` can terminate in register file `σ'`,
using `c` steps and asking exactly the oracle queries listed in `tr`. -/
inductive Exec (O : Oracle) : Stmt → Regs → Regs → ℕ → List Str → Prop
  | noop {σ} : Exec O .noop σ σ 1 []
  | pushBit {i b σ} : Exec O (.pushBit i b) σ (upd σ i (σ i ++ [b])) 1 []
  | tail {i σ} : Exec O (.tail i) σ (upd σ i (σ i).tail) 1 []
  | clear {i σ} : Exec O (.clear i) σ (upd σ i []) 1 []
  | app {i j σ} : Exec O (.app i j) σ (upd σ i (σ i ++ σ j)) (1 + (σ j).length) []
  | query {i j σ} (b : Bool) (h : O (σ j) ↔ b = true) :
      Exec O (.query i j) σ (upd σ i [b]) 1 [σ j]
  | guess {i σ} (b : Bool) : Exec O (.guess i) σ (upd σ i (σ i ++ [b])) 1 []
  | seq {s t σ σ' σ'' c c' tr tr'} : Exec O s σ σ' c tr → Exec O t σ' σ'' c' tr' →
      Exec O (.seq s t) σ σ'' (c + c') (tr ++ tr')
  | whileF {i s σ} (h : σ i = []) : Exec O (.whileNE i s) σ σ 1 []
  | whileT {i s σ σ' σ'' c c' tr tr'} (h : σ i ≠ []) :
      Exec O s σ σ' c tr → Exec O (.whileNE i s) σ' σ'' c' tr' →
      Exec O (.whileNE i s) σ σ'' (1 + c + c') (tr ++ tr')
  | ifT {i s t σ σ' c tr} (h : (σ i).head? = some true) : Exec O s σ σ' c tr →
      Exec O (.ifTrue i s t) σ σ' (1 + c) tr
  | ifF {i s t σ σ' c tr} (h : (σ i).head? ≠ some true) : Exec O t σ σ' c tr →
      Exec O (.ifTrue i s t) σ σ' (1 + c) tr

/-- The initial register file on input `x`: the input sits in register `0`. -/
