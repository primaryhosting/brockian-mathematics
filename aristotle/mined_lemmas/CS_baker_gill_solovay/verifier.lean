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

import RequestProject.BGS.PartA
import RequestProject.BGS.PartB

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Statement: There are oracles A,B with P^A=NP^A and P^B≠NP^B (relativization barrier).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header block above is placed after the `import` lines because Lean 4 requires
`import` commands to come first in a file.)

The model of relativized computation is developed in `RequestProject.BGS.Model`:

* an *oracle* is a set of binary strings, `Oracle := Str → Bool`;
* an *oracle machine* `OM` is a pair of computable functions `ask`, `out`: `ask z l`
  returns the next query on input `z` (a pair of an input and a certificate) given the
  list `l` of oracle answers received so far, and `out z l` returns the verdict;
* `Bounded M k` says that all queries of `M` have length at most `(|x|+2)^k`, where `x`
  is the proper input, and a machine is run for `(|x|+2)^k` steps;
* `Po A L` (`L ∈ P^A`) and `NPo A L` (`L ∈ NP^A`) are the usual definitions, and
  `PClass A`, `NPClass A` are the corresponding classes of languages.

`RequestProject.BGS.PartA` builds an oracle `A` (by recursion on the length of strings)
which encodes acceptance of the `NP^A` computations, so that `P^A = NP^A`.

`RequestProject.BGS.PartB` builds an oracle `B` by diagonalization, so that the unary
language `LB = {1^n : B contains a string of length n}` lies in `NP^B` but not in `P^B`.
-/

namespace CS

/-- **Baker–Gill–Solovay theorem** (the relativization barrier): there is an oracle `A`
with `P^A = NP^A` and an oracle `B` with `P^B ≠ NP^B`. -/

def verifier : OM where
  ask := fun z _ => if z.2.length ≤ z.1.length then z.2 else []
  out := fun z l => if z.1 = ones z.2.length then l.headI else false
  ask_computable := by
    have hc : PrimrecPred (fun p : (Str × Str) × List Bool => p.1.2.length ≤ p.1.1.length) :=
      PrimrecRel.comp Primrec.nat_le
        (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
    have h : Primrec (fun p : (Str × Str) × List Bool =>
        if p.1.2.length ≤ p.1.1.length then p.1.2 else ([] : Str)) :=
      Primrec.ite hc (Primrec.snd.comp Primrec.fst) (Primrec.const [])
    have h2 : Computable (fun p : (Str × Str) × List Bool =>
        if p.1.2.length ≤ p.1.1.length then p.1.2 else ([] : Str)) := h.to_comp
    exact h2
  out_computable := by
    have hc : PrimrecPred (fun p : (Str × Str) × List Bool => p.1.1 = ones p.1.2.length) :=
      PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.fst)
        (primrec_ones.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)))
    have h : Primrec (fun p : (Str × Str) × List Bool =>
        if p.1.1 = ones p.1.2.length then p.2.headI else false) :=
      Primrec.ite hc (Primrec.list_headI.comp Primrec.snd) (Primrec.const false)
    have h3 : Computable (fun p : (Str × Str) × List Bool =>
        if p.1.1 = ones p.1.2.length then p.2.headI else false) := h.to_comp
    exact h3

