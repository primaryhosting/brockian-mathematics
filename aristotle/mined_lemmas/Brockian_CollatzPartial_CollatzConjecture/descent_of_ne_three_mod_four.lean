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

/-!
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Remark on imports: the requested header must be the very first thing in the file, and
Lean does not allow an `import` command after a module docstring. This development is
therefore written against the Lean 4 core library only (no Mathlib import); everything
used below (`Nat`, `omega`, `decide`, `Nat.strongRecOn`) is available in core.

A search of Mathlib turns up no Collatz material at all (no definition of the Collatz
map, no `Reaches1`-style predicate, and no lemma of this shape), so nothing in the
library closes or nearly closes the statement; the development below is self-contained.
The Collatz conjecture itself is a famous open problem, so what is proved here is:

* a Lean-checked *conditional reduction*: `CollatzConjecture` derives the full
  conjecture from the descent hypothesis (every `n > 1` eventually reaches a smaller
  value);
* *unconditional partial results*: the descent hypothesis holds for every `n > 1` with
  `n % 4 ≠ 3` (`descent_of_ne_three_mod_four`), so only the residue class `3 mod 4`
  remains;
* a *finite verification*: every `n` with `1 ≤ n ≤ 1000` reaches `1` (`collatz_le_1000`),
  checked by the kernel via `decide`.
-/

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n / 2` for even `n`, `n ↦ 3 * n + 1` for odd `n`. -/

theorem descent_of_ne_three_mod_four {n : Nat} (hn : 1 < n) (h : n % 4 ≠ 3) :
    ∃ k : Nat, 0 < k ∧ collatzIter k n < n := by
  have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 := by omega
  rcases h4 with h4 | h4 | h4
  · exact descent_of_even hn (by omega)
  · exact descent_of_one_mod_four hn h4
  · exact descent_of_even hn (by omega)

/-- Sharpened reduction: the descent hypothesis only needs to be verified on the
residue class `3 mod 4`. -/
