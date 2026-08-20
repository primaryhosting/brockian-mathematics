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

theorem mach_surjective : Function.Surjective mach := (exists_surjective_nat OM).choose_spec

end CS

/-
# An oracle `B` with `P^B ≠ NP^B`

The oracle `B` is built by diagonalization against all pairs (machine, polynomial
degree).  At stage `j` a fresh length `Nst j` is chosen, so large that the time bound of
the `j`-th machine on inputs of that length is smaller than `2 ^ (Nst j)` and larger
lengths are never touched again.  The `j`-th machine is run on `1 ^ (Nst j)` with the
oracle built so far; if it accepts, no string of length `Nst j` is added to `B`; if it
rejects, a string of length `Nst j` that it did not query is added.

The unary language `LB = {1^n : B contains a string of length n}` is then in `NP^B` but
not in `P^B`.
-/
import RequestProject.BGS.Aux

namespace CS

/-! ## Enumeration of pairs (machine, degree) -/

/-- The machine of the `j`-th pair. -/
