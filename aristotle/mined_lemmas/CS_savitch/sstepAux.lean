/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module documentation, so the header above is
-- written as a plain comment; it is repeated as the module docstring below.)
import RequestProject.Savitch.Final

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The machine model is the standard off-line random-access model of space bounded computation
(see `RequestProject/Savitch/Model.lean`): the memory of a machine is a bit string, one step
rewrites the memory using the memory content and a single input bit, read at a position which
is determined by the memory, and the space used on an input is the maximal length of a memory
string occurring in the computation.

`NSPACE f` and `DSPACE g` are the classes of languages accepted by nondeterministic,
respectively deterministic, machines running in space `O (f n)`, respectively `O (g n)`.

The proof is Savitch's: for a nondeterministic machine `M` running in space `S` on the input
`x`, deciding whether `M` accepts amounts to deciding reachability in the configuration graph
of `M` on `x`, whose vertices are the words of length at most `S`.  Reachability by a path of
length at most `2 ^ k` is decided by the midpoint recursion `savR`, whose recursion depth is
`k`; taking `k = S + 1` suffices because there are only `2 ^ (S + 1) - 1` configurations.  The
simulator runs this recursion with an explicit stack of at most `S + 2` frames, each holding
three words of length at most `S`, so it uses `O (S ^ 2)` bits.  Since the simulator does not
know `S`, it runs the whole procedure for stages `s = 0, 1, 2, …`, and at each stage also
checks whether some reachable configuration has a successor of length more than `s`; the first
stage at which this check fails gives the correct answer, and this happens at the latest at
stage `S`.
-/

namespace CS

namespace Savitch

/-- A deterministic machine viewed as a nondeterministic machine. -/

def sstepAux (M : NMachine) (bit : Option Bool) (σ : SState) : SState :=
  match σ.inner with
  | Inner.call 0 a b => { σ with inner := Inner.ret ((a == b) || leafEdge M bit a b) }
  | Inner.call (k + 1) a b =>
      if a = b then { σ with inner := Inner.ret true }
      else { σ with inner := Inner.call k a [],
                    stack := ⟨k, a, b, [], false⟩ :: σ.stack }
  | Inner.ret v =>
      match σ.stack with
      | [] =>
          let acc' := σ.acc || (v && (M.verdict σ.target == some true))
          let esc' := σ.esc || (v && escapes M bit σ.stage σ.target)
          match univNext σ.stage σ.target with
          | some t' =>
              { σ with target := t', acc := acc', esc := esc',
                       inner := Inner.call (σ.stage + 1) [] t' }
          | none =>
              if acc' then { σ with acc := acc', esc := esc', done := some true }
              else if esc' then
                ⟨σ.stage + 1, [], false, false, Inner.call (σ.stage + 2) [] [], [], none⟩
              else { σ with acc := acc', esc := esc', done := some false }
      | fr :: rest =>
          if fr.second then
            (if v then { σ with inner := Inner.ret true, stack := rest }
             else advanceMid σ fr rest)
          else
            (if v then { σ with inner := Inner.call fr.k fr.mid fr.b,
                                stack := { fr with second := true } :: rest }
             else advanceMid σ fr rest)

/-- The transition of the simulator. -/
