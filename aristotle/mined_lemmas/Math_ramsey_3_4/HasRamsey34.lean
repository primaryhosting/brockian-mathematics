import Mathlib
/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

/-- `MonoClique c b T` says that all pairs of distinct vertices of `T` get colour `b`
under the (edge-)colouring `c`. -/

lemma HasRamsey34.mono {n m : ℕ} (h : HasRamsey34 n) (hnm : n ≤ m) : HasRamsey34 m := by
  intro c hsymm
  have key : ∀ (b : Bool) (T : Finset (Fin n)),
      MonoClique (fun i j => c (Fin.castLE hnm i) (Fin.castLE hnm j)) b T →
      MonoClique c b (T.map ⟨Fin.castLE hnm, Fin.castLE_injective hnm⟩) := by
    intro b T hT x hx y hy hxy
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨a', ha', rfl⟩ := hy
    exact hT a ha a' ha' (fun hab => hxy (by rw [hab]))
  rcases h (fun i j => c (Fin.castLE hnm i) (Fin.castLE hnm j)) (fun x y => hsymm _ _) with
    ⟨T, hT, hm⟩ | ⟨T, hT, hm⟩
  · exact Or.inl ⟨_, by simpa using hT, key _ _ hm⟩
  · exact Or.inr ⟨_, by simpa using hT, key _ _ hm⟩

/-- **R(3,4) = 9**: nine is the least `n` such that every 2-colouring of the edges of `Kₙ`
contains a triangle in the first colour or a `K₄` in the second colour. -/
