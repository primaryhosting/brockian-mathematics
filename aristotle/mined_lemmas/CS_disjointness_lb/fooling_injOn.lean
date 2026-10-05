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

theorem fooling_injOn {n m : ℕ} (P : RandProtocol (Fin n → Bool) (Fin n → Bool) m)
    (hsound : ∀ x y, ¬ Disj x y → P.acc x y = 0) (i : Fin m) :
    Set.InjOn (fun S : Fin n → Bool => (P.proto i).code S (fun j => !S j))
      ↑((Finset.univ : Finset (Fin n → Bool)).filter
        fun S => (P.proto i).run S (fun j => !S j) = true) := by
  intro S hS T hT hcode
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hS hT
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, S j ≠ T j := by
    by_contra hall
    exact hne (funext fun j => by simpa using not_exists.1 hall j)
  -- in either case a mixed, intersecting pair is accepted by `P.proto i`
  have main : ∀ (A B : Fin n → Bool), A j = true → B j = false →
      (P.proto i).code A (fun k => !A k) = (P.proto i).code B (fun k => !B k) →
      (P.proto i).run A (fun k => !A k) = true → False := by
    intro A B hA hB hcode' hrun
    obtain ⟨-, h2⟩ := (P.proto i).rect A B (fun k => !A k) (fun k => !B k) hcode'
    have hacc : P.acc A (fun k => !B k) = 0 := hsound _ _ (not_disj_of_ne j hA hB)
    have := P.run_false_of_acc_zero hacc i
    rw [this, hrun] at h2
    exact Bool.noConfusion h2
  cases hSj : S j with
  | false =>
      have hTj : T j = true := by
        cases hTj' : T j
        · exact absurd (hSj.trans hTj'.symm) hj
        · rfl
      exact main T S hTj hSj hcode.symm hT
  | true =>
      have hTj : T j = false := by
        cases hTj' : T j
        · rfl
        · exact absurd (hSj.trans hTj'.symm) hj
      exact main S T hSj hTj hcode hS

/-- **Set disjointness has `Ω(n)` randomized communication complexity.**

Any public-coin randomized protocol `P` that

* never accepts a pair of intersecting sets (`hsound`), and
* accepts every pair of disjoint sets with probability at least `1/2` (`hcomp`),

must exchange at least `n - 2` bits in the worst case. -/
