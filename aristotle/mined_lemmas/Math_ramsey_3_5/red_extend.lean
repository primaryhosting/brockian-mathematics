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
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open SimpleGraph Finset

/-- `Arrows N s t` says that every simple graph on at least `N` vertices contains
either a clique of size `s` or an independent set of size `t`
(i.e. `N → (s, t)` in the arrow notation for Ramsey numbers). -/

lemma red_extend {m s t : ℕ} (harr : Arrows m s (t + 1))
    (G : SimpleGraph V) (v : V) (A : Finset V) (hA : ∀ x ∈ A, G.Adj v x) (hcard : m ≤ A.card)
    (h1 : G.CliqueFree (s + 1)) (h2 : Gᶜ.CliqueFree (t + 1)) : False := by
  classical
  have hB : (SimpleGraph.induce (↑A : Set V) G)ᶜ.CliqueFree (t + 1) := by
    rw [induce_compl]; exact cliqueFree_induce _ h2
  have hcard' : m ≤ Fintype.card ↥(↑A : Set V) := by simpa using hcard
  have hA' : ¬ (SimpleGraph.induce (↑A : Set V) G).CliqueFree s := fun hx =>
    harr _ _ hcard' ⟨hx, hB⟩
  rw [SimpleGraph.CliqueFree] at hA'
  push_neg at hA'
  obtain ⟨T, hT⟩ := hA'
  have hT' : G.IsNClique s (T.map (Function.Embedding.subtype _)) := isNClique_of_induce hT
  have hv : ∀ b ∈ T.map (Function.Embedding.subtype (fun x => x ∈ (↑A : Set V))), G.Adj v b := by
    intro b hb
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hb
    obtain ⟨x, -, rfl⟩ := hb
    exact hA _ (Finset.mem_coe.mp x.2)
  exact h1 _ (hT'.insert hv)

/-- If `v` has a set `A` of at least `n` non-neighbours (all distinct from `v`) and
`Arrows n (s+1) t` holds, then `G` has an `(s+1)`-clique or `Gᶜ` has a `(t+1)`-clique. -/
