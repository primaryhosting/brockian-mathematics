import Mathlib
import RequestProject.WriteIntegrity

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

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A formal model of the write-integrity check of an isolation engine

This file formalises a small but faithful model of the *write path* of a
sandboxing / isolation engine (a protected compartment architecture, `PCA`).

The machine has a `wordBits`-bit address space, so addresses are naturals taken
modulo `N = 2 ^ wordBits`.  A compartment is described by a single `bound`: the
compartment may only write to addresses strictly below `bound`.

A write request `Req` consists of a start address, a size (number of cells
written) and a value.  The set of cells that the hardware actually touches is
`touched r`; note that the address computation *wraps around* the address space,
which is exactly what real hardware does.

Two bounds checks are modelled:

* `checkBuggy` : the classical "`addr + size ≤ bound`" check performed with
  machine (i.e. wrapping) arithmetic;
* `checkSafe`  : the same check performed with exact arithmetic.

Main results:

* `checkSafe_sound` / `checkSafe_complete` / `checkSafe_iff_sandboxed`:
  the safe check is sound and complete for the sandboxing property, so the
  engine's model exactly characterises the admissible writes.
* `checkSafe_preserves_outside`, `run_preserves_outside`: the isolation theorem
  — a whole run of accepted requests never modifies memory outside the
  compartment.
* `with_check_true_admits_forge`: the buggy check is *unsound* — there is a
  request that it accepts (`check = true`) yet which escapes the compartment,
  i.e. a forged write is admitted.
* `forge_escapes_sandbox`: that forgery really does corrupt memory outside the
  compartment.
* `checkBuggy_complete` and `checkBuggy_eq_checkSafe_of_noOverflow`: the buggy
  check is nevertheless complete and agrees with the safe check whenever the
  address computation does not overflow, so overflow is precisely the source of
  the unsoundness.
-/

namespace PCA
namespace WriteIntegrity

/-- Width of the machine address space, in bits. -/

lemma N_pos : 0 < N := Nat.two_pow_pos wordBits

/-- A memory maps addresses to values. -/
abbrev Mem := ℕ → ℕ

/-- A write request: write `val` into `size` consecutive cells starting at `addr`. -/
structure Req where
  /-- Start address of the write. -/
  addr : ℕ
  /-- Number of consecutive cells written. -/
  size : ℕ
  /-- Value written into each of those cells. -/
  val : ℕ
deriving DecidableEq, Repr

/-- The set of memory cells physically touched by a request.  Address arithmetic
wraps around the address space, as it does on real hardware. -/
