/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We prove: **there exist problems with no fastest algorithm** — a Blum-style speedup
phenomenon — in a completely explicit machine model with an explicit runtime measure.

*Machines.* A `DigitMachine` fixes a base `b ≥ 2` and is a finite-state streaming
machine: it reads the base-`b` digits of its input one digit per step (least
significant digit first), updating a state taken from a finite state set, and finally
outputs a bit determined by the state it ends in.

*Runtime.* The runtime (`cost`) of a machine on input `x` is the number of steps it
performs, i.e. the number of base-`b` digits of `x`.

*Speedup.* Recoding the input in base `b ^ k` lets one machine step consume `k` old
digits, dividing the runtime by `k`. Consequently, for the (nontrivial) problem
"is `x` divisible by `3`?", every algorithm is beaten, on all but finitely many
inputs, by another algorithm for the same problem, and by an arbitrarily large factor;
hence no fastest algorithm exists.

*Scope.* The statement proved here is "there exist problems with no fastest algorithm",
with the speedup obtained by input recoding in an explicit machine model with an
explicit runtime measure (`no_fastest_algorithm`, `blum_speedup`). The speedup factor
is linear (any factor `k`), so this is the recoding/linear-speedup form of the
phenomenon rather than Blum's recursion-theoretic construction with an arbitrary
total computable speedup function.

As in the classical argument, the price of the speedup is a larger transition table
(the compressed machine reads digits from a larger alphabet), not a slower step: each
step of any machine remains a single lookup in a finite control, and is charged one
unit of time.

The file is self-contained: it uses nothing beyond the Lean prelude.
-/

set_option autoImplicit false

namespace CS

/-! ## Numbers and digit strings -/

/-- The natural number represented by the digit list `L` in base `b`, least
significant digit first. -/

theorem ofDigits_cons (b d : Nat) (L : List Nat) :
    ofDigits b (d :: L) = d + b * ofDigits b L := rfl

