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

theorem immerman_szelepcsenyi_configGraph (stepV : V → V → Bool) (v₀ v₁ : V) :
    (Accepts (Fintype.card V) (gOf stepV) (enc v₀) (enc v₁) ↔
        ¬ Relation.ReflTransGen (fun a b => stepV a b = true) v₀ v₁) ∧
      (∀ w, Relation.ReflTransGen (Step (Fintype.card V) (gOf stepV) (enc v₀) (enc v₁)) init w →
        w ∈ Box (Fintype.card V + 2)) ∧
      (Box (Fintype.card V + 2)).card ≤ 6 * (Fintype.card V + 2) ^ 8 := by
  obtain ⟨hiff, hbox, hcard⟩ :=
    immerman_szelepcsenyi (g := gOf stepV) (enc_lt v₀) (enc_lt v₁) (fun u v h => gOf_lt stepV h)
  refine ⟨?_, hbox, hcard⟩
  rw [hiff]
  constructor
  · intro h hreach
    exact h (reflTransGen_gOf hreach)
  · intro h hreach
    obtain ⟨y, hy, hy2⟩ := reflTransGen_of_gOf hreach
    have : y = v₁ := (Fintype.equivFin V).injective (Fin.ext hy.symm)
    exact h (this ▸ hy2)

end ConfigGraph

end CS

