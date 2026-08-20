import Mathlib

/-!
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
Statement: The Kruskal–Katona theorem on shadows of set systems.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` lines to precede any module doc comment, so the required
header appears immediately after the single `import Mathlib` line.)
-/

open Finset
open scoped FinsetFamily

namespace Math2

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Taking shadows commutes with pushing a family forward along an embedding. -/

lemma shadow_iterate_image_map (f : α ↪ β) (𝒜 : Finset (Finset α)) (k : ℕ) :
    ∂^[k] (𝒜.image (Finset.map f)) = (∂^[k] 𝒜).image (Finset.map f) := by
  induction k generalizing 𝒜 with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      shadow_image_map, ih]

/-- A family of finsets of naturals all of whose elements are `< n` is the pushforward of a
family of finsets of `Fin n`. -/
