import Mathlib

/-!
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset
open scoped FinsetFamily

namespace Math2

/-- Pushing a family of subsets of `Fin n` forward into `ℕ` commutes with taking shadows. -/

lemma shadow_iterate_image_map_valEmbedding {n : ℕ} (i : ℕ) (ℬ : Finset (Finset (Fin n))) :
    ∂^[i] (ℬ.image (Finset.map Fin.valEmbedding))
      = (∂^[i] ℬ).image (Finset.map Fin.valEmbedding) := by
  induction i generalizing ℬ with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      shadow_image_map_valEmbedding, ih]

/-- Every family of finite sets of naturals bounded by `n` comes from a family of subsets
of `Fin n`. -/
