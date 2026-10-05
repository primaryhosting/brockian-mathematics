/-
# Kruskal Katona
Category: Frontier Math
Target: Math2.kruskal_katona
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- Shadows commute with taking the image of a family along an injective map. -/

lemma shadow_iterate_image_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (i : ℕ) (𝒜 : Finset (Finset α)) :
    ∂^[i] (𝒜.image (Finset.image f)) = (∂^[i] 𝒜).image (Finset.image f) := by
  induction i generalizing 𝒜 with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      shadow_image_of_injective hf, ih]

/-- **Kruskal–Katona theorem** (Lovász form), for families of finite sets of natural numbers.

If `𝒜` is a family of `r`-element subsets of `ℕ` with `#𝒜 ≥ k.choose r` (where `r ≤ k`), then for
every `i ≤ r` the `i`-th iterated shadow of `𝒜` has size at least `k.choose (r - i)`. -/
