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

theorem oracleA_spec (i k : ℕ) (x : Str) (hb : Bounded (mach i) k) :
    oracleA (pad i k x) = true ↔
      ∃ y : Str, y.length ≤ tb k x ∧ runB (mach i) oracleA (x, y) (tb k x) = true := by
  classical
  set q := pad i k x with hq
  set n := q.length with hn
  have hlt : tb k x < n := hn ▸ tb_lt_pad_length i k x
  have hagree : ∀ q' : Str, q'.length < n → oracleA q' = Alen n q' := by
    intro q' h'
    exact (Alen_eq_oracleA n q' h').symm
  have hrun : ∀ y : Str, runB (mach i) oracleA (x, y) (tb k x)
      = runB (mach i) (Alen n) (x, y) (tb k x) :=
    fun y => runB_congr_len (mach i) k hb (Alen n) oracleA (x, y) n hlt hagree _
  have hdef : oracleA q =
      decide (∃ (i' k' : ℕ) (x' : Str), pad i' k' x' = q ∧ ∃ y : Str, y.length ≤ tb k' x' ∧
        runB (mach i') (Alen n) (x', y) (tb k' x') = true) := by
    have h0 : oracleA q = Alen (n + 1) q := rfl
    rw [h0, Alen]
    simp only
    rw [if_pos rfl]
  rw [hdef, decide_eq_true_iff]
  constructor
  · rintro ⟨i', k', x', hpad, y, hy, hacc⟩
    obtain ⟨rfl, rfl, rfl⟩ := pad_inj (hq ▸ hpad.symm : pad i k x = pad i' k' x')
    exact ⟨y, hy, by rw [hrun]; exact hacc⟩
  · rintro ⟨y, hy, hacc⟩
    exact ⟨i, k, x, hq.symm, y, hy, by rw [← hrun]; exact hacc⟩

/-! ## The deterministic machine that queries `A` -/

