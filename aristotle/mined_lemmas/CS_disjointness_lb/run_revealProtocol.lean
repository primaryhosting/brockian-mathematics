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

/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Disjointness Lb

Set disjointness on `n`-bit inputs has `Ω(n)` randomized communication
complexity: any public-coin randomized protocol which never accepts a pair of
intersecting sets, and accepts every pair of disjoint sets with probability at
least `1/2`, must communicate at least `n - 2` bits in the worst case.

The proof is the classical fooling-set argument combined with an averaging step
over the public coin:

* the `2 ^ n` pairs `(S, Sᶜ)` are all disjoint, hence each is accepted with
  probability at least `1/2`;
* averaging, some deterministic protocol in the support accepts at least
  `2 ^ n / 2` of them;
* by the rectangle property of protocols, two distinct such pairs cannot produce
  the same transcript (otherwise a mixed, intersecting pair `(S, Tᶜ)` would also
  be accepted, which is forbidden);
* a protocol of cost `c` has fewer than `2 ^ (c + 1)` transcripts, whence
  `2 ^ n / 2 ≤ 2 ^ (c + 1)`, i.e. `n ≤ c + 2`.

The randomized model formalized here is the one-sided error (public-coin) model:
errors are allowed only on disjoint pairs, and there the acceptance probability
need only exceed `1/2`.  The bound `n ≤ cost + 2` is tight up to an additive
constant, as witnessed by `CS.disjointness_ub`.
-/

namespace CS

/-! ## Deterministic communication protocols

A deterministic two-party protocol is a binary tree.  At an `alice` node the
first player sends one bit, computed from her input `x : X`; at a `bob` node the
second player sends one bit computed from his input `y : Y`.  A `leaf` carries
the output of the protocol.
-/

/-- A deterministic communication protocol tree for inputs `X` (Alice) and `Y` (Bob). -/
inductive Protocol (X Y : Type) : Type
  | leaf (b : Bool) : Protocol X Y
  | alice (f : X → Bool) (t0 t1 : Protocol X Y) : Protocol X Y
  | bob (g : Y → Bool) (t0 t1 : Protocol X Y) : Protocol X Y

namespace Protocol

variable {X Y : Type}

/-- The output of the protocol on the input pair `(x, y)`. -/

theorem run_revealProtocol {n : ℕ} :
    ∀ (l : List (Fin n)) (xg x y : Fin n → Bool), (∀ j, j ∉ l → xg j = x j) →
      (revealProtocol l xg).run x y = decide (Disj x y) := by
  intro l
  induction l with
  | nil =>
      intro xg x y h
      have hx : xg = x := funext fun j => h j (by simp)
      subst hx
      simp [revealProtocol, Protocol.run]
  | cons j l ih =>
      intro xg x y h
      have hupd : ∀ k, k ∉ l → Function.update xg j (x j) k = x k := by
        intro k hk
        by_cases hkj : k = j
        · subst hkj; simp
        · rw [Function.update_of_ne hkj]
          exact h k (by simp [hkj, hk])
      cases hxj : x j
      · have := ih (Function.update xg j false) x y (by simpa [hxj] using hupd)
        simp [revealProtocol, Protocol.run, hxj, this]
      · have := ih (Function.update xg j true) x y (by simpa [hxj] using hupd)
        simp [revealProtocol, Protocol.run, hxj, this]

/-- The hypotheses of `CS.disjointness_lb` are satisfiable: there is a protocol
of cost `n + 1` which computes disjointness exactly. -/
