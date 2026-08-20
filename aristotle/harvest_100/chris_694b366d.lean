import Mathlib

/-!
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
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

namespace CS

namespace Aux

variable {T : Type*}

/-- `List.replicate i y` flattened is a member of the Kleene star of `{y}`. -/
lemma flatten_replicate_mem_kstar (y : List T) (i : ℕ) :
    (List.replicate i y).flatten ∈ KStar.kstar ({y} : Language T) := by
  rw [Language.mem_kstar]
  refine ⟨List.replicate i y, rfl, ?_⟩
  intro s hs
  rw [List.eq_of_mem_replicate hs]
  exact Set.mem_singleton _

end Aux

/--
**The pumping lemma for regular languages.**

Every regular language `L` over an alphabet `T` admits a pumping length `p > 0` such that every
word `w ∈ L` of length at least `p` can be split as `w = x ++ y ++ z` with `y` nonempty,
`(x ++ y).length ≤ p`, and `x ++ yⁱ ++ z ∈ L` for every `i : ℕ`
(where `yⁱ` is written as the flattening of `List.replicate i y`).
-/
theorem pumping_regular {T : Type} {L : Language T} (hL : L.IsRegular) :
    ∃ p : ℕ, 0 < p ∧ ∀ w ∈ L, p ≤ w.length →
      ∃ x y z : List T, w = x ++ y ++ z ∧ y ≠ [] ∧ (x ++ y).length ≤ p ∧
        ∀ i : ℕ, x ++ (List.replicate i y).flatten ++ z ∈ L := by
  obtain ⟨σ, hσ, M, rfl⟩ := hL
  have hne : Nonempty σ := ⟨M.start⟩
  refine ⟨Fintype.card σ, Fintype.card_pos, ?_⟩
  intro w hw hlen
  obtain ⟨x, y, z, hxyz, hle, hy, hsub⟩ := M.pumping_lemma hw hlen
  refine ⟨x, y, z, hxyz, hy, ?_, ?_⟩
  · simpa [List.length_append] using hle
  · intro i
    refine hsub ?_
    rw [Language.mem_mul]
    refine ⟨x ++ (List.replicate i y).flatten, ?_, z, Set.mem_singleton _, by simp⟩
    rw [Language.mem_mul]
    exact ⟨x, Set.mem_singleton _, _, Aux.flatten_replicate_mem_kstar y i, rfl⟩

end CS

