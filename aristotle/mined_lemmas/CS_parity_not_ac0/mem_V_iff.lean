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
## Characters and low-degree functions over `𝔽₃`

Boolean inputs are encoded multiplicatively: `true ↦ -1`, `false ↦ 1` (`CS.sgn`),
and also additively `true ↦ 1`, `false ↦ 0` (`CS.bit`).

For `S : Finset (Fin n)` the *character* `chi S` is the multilinear monomial
`x ↦ ∏ i ∈ S, sgn (x i)`; `V n D` is the space of functions `(Fin n → Bool) → 𝔽₃`
spanned by characters of degree at most `D`.
-/

namespace CS

/-- The field with three elements. -/
abbrev F : Type := ZMod 3

/-- Boolean inputs on `n` variables. -/
abbrev Inp (n : ℕ) : Type := Fin n → Bool

/-- Multiplicative (`±1`) encoding of a bit. -/

lemma mem_V_iff {n D : ℕ} (f : Inp n → F) :
    f ∈ V n D ↔ ∃ c : Finset (Fin n) → F, ∀ x, f x = ∑ S ∈ gens n D, c S * chi S x := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨S, hS, rfl⟩ := hf
        refine ⟨fun T => if T = S then 1 else 0, fun x => ?_⟩
        rw [Finset.sum_eq_single S]
        · simp
        · intro T _ hT; simp [hT]
        · intro h; exact absurd (mem_gens.2 hS) h
    | zero => exact ⟨0, fun x => by simp⟩
    | add f g _ _ ihf ihg =>
        obtain ⟨cf, hcf⟩ := ihf; obtain ⟨cg, hcg⟩ := ihg
        exact ⟨cf + cg, fun x => by simp [hcf, hcg, add_mul, Finset.sum_add_distrib]⟩
    | smul a f _ ih =>
        obtain ⟨c, hc⟩ := ih
        exact ⟨a • c, fun x => by simp [hc, Finset.mul_sum, mul_assoc]⟩
  · rintro ⟨c, hc⟩
    have : f = ∑ S ∈ gens n D, c S • chi S := by funext x; rw [hc x]; simp
    rw [this]
    exact Submodule.sum_mem _ (fun S hS => Submodule.smul_mem _ _ (chi_mem_V (mem_gens.1 hS)))

/-- Every function on `n` bits has degree at most `n`. -/
