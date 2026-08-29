import RequestProject.QueryProg
import RequestProject.Aux

/-!
# An oracle `A` with `P^A = NP^A`

The oracle answers questions about its own relativized nondeterministic
computations.  This is well defined because the query `encodeQ i x t` is *longer*
than any string that can be queried during a computation of cost at most `t` on
input `x`, so the definition can be made by recursion on the length of the query.
-/

namespace CS

open Prog

/-- `AAux n z` is the value of the oracle at `z`, where `n` is the length of `z`;
the recursive calls are only made at strictly shorter strings. -/

theorem progOf_surjective : Function.Surjective progOf := exists_prog_enum.choose_spec

end CS

import Mathlib

/-!
# A model of oracle computation

This file sets up a concrete, self-contained model of *oracle machines*: a small
imperative language over string registers, with an explicit cost (time) measure,
nondeterministic guessing, and oracle queries.  On top of it we define the
relativized classes `PClass O` and `NPClass O`.
-/

namespace CS

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a set of strings (given as a predicate, classically). -/
abbrev Oracle := Str → Prop

/-- A language is a set of strings. -/
abbrev Language := Str → Prop

/-- Register file: countably many string registers. -/
abbrev Regs := ℕ → Str

/-- A configuration: the registers together with the remaining nondeterministic
guess bits. -/
structure Cfg where
  regs : Regs
  cert : Str

/-- Programs of the machine model.  Register `0` holds the input, register `1`
holds the output. -/
inductive Prog
  | done
  | seq (p q : Prog)
  | clear (i : ℕ)
  | appendBit (i : ℕ) (b : Bool)
  | appendReg (i j : ℕ)
  | pop (i : ℕ)
  | guess (i : ℕ)
  | query (i j : ℕ)
  | loop (i : ℕ) (body : Prog)
  deriving DecidableEq

namespace Prog

/-- `Exec O p c c' n qs` : running program `p` from configuration `c` under oracle
`O` terminates in configuration `c'`, at cost `n`, having asked the oracle
queries `qs` (in order). -/
inductive Exec (O : Oracle) : Prog → Cfg → Cfg → ℕ → List Str → Prop
  | done (c) : Exec O Prog.done c c 1 []
  | seq {p q c1 c2 c3 n1 n2 qs1 qs2} :
      Exec O p c1 c2 n1 qs1 → Exec O q c2 c3 n2 qs2 →
      Exec O (Prog.seq p q) c1 c3 (n1 + n2) (qs1 ++ qs2)
  | clear (i c) :
      Exec O (Prog.clear i) c ⟨Function.update c.regs i [], c.cert⟩ 1 []
  | appendBit (i b c) :
      Exec O (Prog.appendBit i b) c
        ⟨Function.update c.regs i (c.regs i ++ [b]), c.cert⟩ 1 []
  | appendReg (i j c) :
      Exec O (Prog.appendReg i j) c
        ⟨Function.update c.regs i (c.regs i ++ c.regs j), c.cert⟩
        (1 + (c.regs j).length) []
  | pop (i c) :
      Exec O (Prog.pop i) c ⟨Function.update c.regs i (c.regs i).tail, c.cert⟩ 1 []
  | guess {i c b rest} : c.cert = b :: rest →
      Exec O (Prog.guess i) c
        ⟨Function.update c.regs i (c.regs i ++ [b]), rest⟩ 1 []
  | queryT {i j c} : O (c.regs j) →
      Exec O (Prog.query i j) c
        ⟨Function.update c.regs i (c.regs i ++ [true]), c.cert⟩
        (1 + (c.regs j).length) [c.regs j]
  | queryF {i j c} : ¬ O (c.regs j) →
      Exec O (Prog.query i j) c
        ⟨Function.update c.regs i (c.regs i ++ [false]), c.cert⟩
        (1 + (c.regs j).length) [c.regs j]
  | loopDone {i body c} : c.regs i = [] → Exec O (Prog.loop i body) c c 1 []
  | loopStep {i body c c' c'' n1 n2 qs1 qs2} : c.regs i ≠ [] →
      Exec O body c c' n1 qs1 → Exec O (Prog.loop i body) c' c'' n2 qs2 →
      Exec O (Prog.loop i body) c c'' (1 + n1 + n2) (qs1 ++ qs2)

/-- Deterministic programs: those that never guess. -/
