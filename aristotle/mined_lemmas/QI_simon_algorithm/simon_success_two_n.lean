import Mathlib
import RequestProject.QI.Spanning
import RequestProject.QI.Classical

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/--
**Simon's problem is solved with `O(n)` quantum queries but needs `Ω(2 ^ (n / 2))`
classical queries.**

The four conjuncts are:

1. *One quantum query.*  For every Simon function `f` with secret `s`, one run of the
   circuit `H ∘ U_f ∘ H` applied to `|0,0⟩` — which uses exactly one oracle query — yields
   a measurement outcome that is uniformly distributed over the hyperplane
   `s^⊥ = {y | ⟪y, s⟫ = 0}` (probability `2 / 2 ^ n` on it, `0` off it).

2. *`m` quantum queries.*  With `m` runs of the circuit (`m` queries in total), the
   outcomes determine `s` uniquely — i.e. `s` is the only nonzero solution of the linear
   system they define, so Gaussian elimination recovers it — with probability at least
   `1 - 2 ^ n / 2 ^ m`.

3. *`O(n)` queries suffice.*  Taking `m = 2 n` queries, the algorithm succeeds with
   probability at least `1 - 2 ^ (-n)`.

4. *Classical lower bound.*  Any deterministic classical query algorithm (decision tree)
   that outputs the correct secret for every Simon function on `n ≥ 2` bits has depth at
   least `2 ^ (n / 2)`, i.e. makes `Ω(2 ^ (n / 2))` queries in the worst case.
-/

theorem simon_success_two_n {n : ℕ} {f : V n → V n} {s : V n} (h : IsSimon f s) :
    1 - (1 / 2 : ℝ) ^ n ≤ simonSuccess f (2 * n) s := by
  have hb := simon_success_bound h (2 * n)
  have heq : (2:ℝ) ^ n / 2 ^ (2 * n) = (1 / 2 : ℝ) ^ n := by
    rw [pow_mul, div_pow]
    rw [show ((2:ℝ) ^ 2) ^ n = 2 ^ n * 2 ^ n by rw [← pow_mul, ← pow_add]; ring_nf]
    rw [one_pow]
    field_simp
  rwa [heq] at hb

end QI

import RequestProject.QI.Basic

/-!
# Simon's problem: the classical `Ω(2 ^ (n / 2))` lower bound

A deterministic classical query algorithm is a decision tree `DTree n`: each internal node
queries a point `x : V n` and branches on the answer `f x : V n`; leaves output a guess for
the secret.  `DTree.depth` is the worst-case number of queries.

The lower bound: if a tree outputs the correct secret for *every* Simon function on `n`
bits (`n ≥ 2`), then its depth is at least `2 ^ (n / 2)`.
-/

namespace QI

set_option autoImplicit false

/-- A deterministic classical query algorithm for Simon's problem: a decision tree whose
internal nodes query a point and branch on the answer. -/
inductive DTree (n : ℕ) : Type
  | leaf : V n → DTree n
  | node : V n → (V n → DTree n) → DTree n

namespace DTree

/-- The worst-case number of queries made by the tree. -/
