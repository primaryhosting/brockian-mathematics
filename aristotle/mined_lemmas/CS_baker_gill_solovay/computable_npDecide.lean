import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The relativization barrier

We formalize the Baker–Gill–Solovay theorem in a *relativized query model* of
computation:

* A **string** is a `List Bool`, a **language** (equivalently an oracle) is a
  Boolean-valued function on strings.
* An **oracle machine** is given by a *computable* transition function
  `step : α × Trans → Str ⊕ Bool`, which, given the input and the transcript of
  the queries asked so far together with the oracle's answers, either asks a new
  query (`Sum.inl z`) or halts with a verdict (`Sum.inr b`).
* The resource that is counted is the number of steps (each step is either one
  oracle query or the final answer), and a machine is *polynomially bounded*
  when it is run for `c * (n+1)^d` steps on inputs of length `n`.

`PClass A` is the class of languages decided by a polynomially bounded
deterministic oracle machine with oracle `A`; `NPClass A` is the class of
languages accepted with a polynomially long certificate by a polynomially
bounded verifier with oracle `A`.

The theorem `CS.baker_gill_solovay` states that there is an oracle `A` with
`PClass A = NPClass A` and an oracle `B` with `PClass B ≠ NPClass B`.

Two features of this model should be kept in mind. Machines are required to be
computable, so there are only countably many of them, which is what makes the
diagonalization for `B` possible; and the amount of computation performed
between two queries is unrestricted, only the number of steps is. Consequently
the collapsing oracle can be taken to be the empty oracle `emptyLang`: with no
useful oracle, both classes consist exactly of the decidable languages, since a
deterministic machine may scan all polynomially long certificates in a single
step. The separating oracle `B` is built by the usual stage construction: at
stage `i` one diagonalizes against the `i`-th machine at a length `N` where the
machine's step bound is smaller than the number `2 ^ N` of candidate strings.
-/

namespace CS

/-- Strings are finite bit sequences. -/
abbrev Str := List Bool

/-- A language, equivalently an oracle, is an indicator function on strings. -/
abbrev Lang := Str → Bool

/-- A transcript records the queries made so far together with their answers. -/
abbrev Trans := List (Str × Bool)

/-- An oracle machine with input type `α`: a computable function which, from the
input and the transcript so far, either issues a new oracle query or halts with
a verdict. -/
structure Machine (α : Type) [Primcodable α] : Type where
  /-- The transition function. -/
  step : α × Trans → Str ⊕ Bool
  /-- The transition function is computable. -/
  hstep : Computable step

section Model

variable {α : Type} [Primcodable α]

/-- A configuration: the input, the transcript so far, and the verdict (if the
machine has already halted). -/
abbrev Config (α : Type) := α × Trans × Option Bool

/-- One step of the machine with oracle `O`. -/

lemma computable_npDecide (V : Machine (Str × Str)) (A : Lang) (hA : Computable A) (c d : ℕ) :
    Computable (npDecide V A c d) := by
  have hm : Computable (fun x : Str => polyBound c d x.length) :=
    (Primrec.nat_mul.comp (Primrec.const c)
      ((Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.succ.comp Primrec.list_length)
        (Primrec.const d))).to_comp
  have hlist : Computable (fun x : Str => allStrLe (polyBound c d x.length)) :=
    primrec_allStrLe.to_comp.comp hm
  have hcert : Computable (fun q : Str × ℕ =>
      (allStrLe (polyBound c d q.1.length))[q.2]?.getD ([] : Str)) :=
    Computable.option_getD
      (Computable.list_getElem?.comp (hlist.comp Computable.fst) Computable.snd)
      (Computable.const [])
  have hP : Computable₂ (fun (x : Str) (i : ℕ) =>
      (run V A (x, (allStrLe (polyBound c d x.length))[i]?.getD [])
        (polyBound c d x.length)).getD false) :=
    Computable.option_getD
      ((computable_run V A hA).comp (Computable.pair Computable.fst hcert)
        (hm.comp Computable.fst))
      (Computable.const false)
  have hrec := Computable.nat_rec
    (f := fun x : Str => (allStrLe (polyBound c d x.length)).length)
    (g := fun _ : Str => false)
    (h := fun (x : Str) (q : ℕ × Bool) =>
      (run V A (x, (allStrLe (polyBound c d x.length))[q.1]?.getD [])
        (polyBound c d x.length)).getD false || q.2)
    (Computable.list_length.comp hlist) (Computable.const false)
    ((Primrec.dom_bool₂ (fun a b : Bool => a || b)).to_comp.comp
      (hP.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd))
  refine hrec.of_eq fun x => ?_
  exact existsUpto_rec (fun i => (run V A (x, (allStrLe (polyBound c d x.length))[i]?.getD [])
    (polyBound c d x.length)).getD false) _

