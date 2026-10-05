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
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

We set up two-party communication protocols as protocol trees, and prove the
`Ω(n)` lower bound for the randomized communication complexity of set
disjointness on `n`-element ground sets: any public-coin randomized protocol
which never wrongly claims that two intersecting sets are disjoint, and which
detects disjointness with probability at least `1/2`, must communicate at least
`n - 1` bits (`CS.disjointness_lb`).

The proof combines the classical fooling set `{(S, Sᶜ) : S ⊆ Fin n}` of size
`2 ^ n` for disjointness with an averaging argument over the public random
string.  We also record the matching upper bound `n + 1`
(`CS.disjointness_ub`), which shows in particular that the hypotheses of the
lower bound are satisfiable, and the deterministic lower bound `n`
(`CS.disjointness_deterministic_lb`).

The randomized bound proved here is for protocols with one-sided error (they
never certify disjointness wrongly); the two-sided bounded-error case is
Razborov's theorem and is not covered by this argument.
-/

open Finset

namespace CS

open scoped Classical

/-- A deterministic two-party communication protocol tree.  `alice g L R` means
"Alice sends the bit `g x` and the players continue with `L` (if the bit is
`true`) or `R` (if it is `false`)"; `bob` is the same with Bob speaking. -/
inductive Prot (X Y : Type*) : Type _
  | leaf : Bool → Prot X Y
  | alice : (X → Bool) → Prot X Y → Prot X Y → Prot X Y
  | bob : (Y → Bool) → Prot X Y → Prot X Y → Prot X Y

namespace Prot

variable {X Y : Type*}

/-- The output of the protocol on the input pair `(x, y)`. -/

theorem accepted_fooling_le {n : ℕ} (P : Prot (Fin n → Bool) (Fin n → Bool))
    (hsound : ∀ a b, P.run a b = true → Disj a b) :
    ((univ : Finset (Fin n → Bool)).filter
      (fun S => P.run S (cmpl S) = true)).card ≤ 2 ^ P.cost := by
  refine fooling_card_le (X := Fin n → Bool) (Y := Fin n → Bool)
    (univ : Finset (Fin n → Bool)) id cmpl Disj
    (fun i _ j _ hij => fooling_pairs i j hij)
    P (fun _ => True) (fun _ => True) _ (Finset.filter_subset _ _) ?_
    (fun a b _ _ hrun => hsound a b hrun)
  intro i hi
  rw [Finset.mem_filter] at hi
  exact ⟨trivial, trivial, hi.2⟩

/-- The `m`-th bit of a subset of `Fin n` (`false` if `m` is out of range). -/
