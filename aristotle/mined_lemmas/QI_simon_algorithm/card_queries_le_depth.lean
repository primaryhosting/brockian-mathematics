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

lemma card_queries_le_depth {n : ℕ} (t : DTree n) (f : V n → V n) :
    (t.queries f).card ≤ t.depth := by
  induction t with
  | leaf a => simp [queries, depth]
  | node x k ih =>
    rw [queries, depth]
    have hsup : (k (f x)).depth ≤ (Finset.univ.sup fun b => (k b).depth) :=
      Finset.le_sup (f := fun b => (k b).depth) (Finset.mem_univ (f x))
    calc (insert x ((k (f x)).queries f)).card ≤ ((k (f x)).queries f).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ (k (f x)).depth + 1 := Nat.add_le_add_right (ih (f x)) 1
      _ ≤ (Finset.univ.sup fun b => (k b).depth) + 1 := Nat.add_le_add_right hsup 1
      _ = 1 + Finset.univ.sup fun b => (k b).depth := by ring

/-- Two oracles agreeing on the queried points give the same output. -/
