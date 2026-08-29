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

import Mathlib

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace CS

/-! ## Reachability in a finite directed graph

We work with a directed graph on the vertex set `{0, 1, ..., n-1}` given by a Boolean
adjacency function `g`.  `reachB n g s i v` says that `v` is reachable from `s` by a walk of
length *at most* `i` (we allow "staying put" at each step, so walks of length exactly `i`
with lazy steps are the same thing as walks of length at most `i`). -/

section Graph

variable (n : ℕ) (g : ℕ → ℕ → Bool) (s : ℕ)

/-- `reachB n g s i v = true` iff `v` is reachable from `s` in at most `i` steps
(inside the vertex set `{0,…,n-1}`). -/

lemma reflTransGen_of_gOf {stepV : V → V → Bool} {x : V} {m : ℕ}
    (h : Relation.ReflTransGen (fun a b => gOf stepV a b = true) (enc x) m) :
    ∃ y : V, m = enc y ∧ Relation.ReflTransGen (fun a b => stepV a b = true) x y := by
  induction h with
  | refl => exact ⟨x, rfl, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
      obtain ⟨y, rfl, hy⟩ := ih
      obtain ⟨-, hc⟩ := gOf_lt stepV hbc
      refine ⟨(Fintype.equivFin V).symm ⟨c, hc⟩, (enc_symm hc).symm, hy.tail ?_⟩
      show stepV y ((Fintype.equivFin V).symm ⟨c, hc⟩) = true
      rw [← gOf_enc stepV y ((Fintype.equivFin V).symm ⟨c, hc⟩), enc_symm hc]
      exact hbc

/-- **Immerman-Szelepcsenyi theorem for an arbitrary finite configuration graph.**
Given a nondeterministic machine whose configuration graph is `stepV` on the finite type `V`,
with initial configuration `v₀` and accepting configuration `v₁`, the inductive counting machine
run on the encoded graph accepts exactly when `v₁` is *not* reachable from `v₀`, and it visits at
most `6 * (|V| + 2) ^ 8` configurations. -/
