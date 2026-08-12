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

namespace CS

/--
**The pumping lemma for regular languages.**

Every regular language `L` admits a pumping length `p > 0` such that every word `w ∈ L`
of length at least `p` can be split as `w = x ++ y ++ z` with `|x ++ y| ≤ p` and `y ≠ []`,
in such a way that all pumped words `x ++ y^i ++ z` (with `y^i` the `i`-fold concatenation
of `y`, written `(List.replicate i y).flatten`) again belong to `L`.
-/
theorem pumping_regular {T : Type} {L : Language T} (hL : L.IsRegular) :
    ∃ p : ℕ, 0 < p ∧ ∀ w ∈ L, p ≤ w.length →
      ∃ x y z : List T, w = x ++ y ++ z ∧ (x ++ y).length ≤ p ∧ y ≠ [] ∧
        ∀ i : ℕ, x ++ (List.replicate i y).flatten ++ z ∈ L := by
  obtain ⟨σ, hσ, M, rfl⟩ := hL
  refine ⟨Fintype.card σ, Fintype.card_pos_iff.mpr ⟨M.start⟩, ?_⟩
  intro w hw hlen
  obtain ⟨a, b, c, hsplit, hab, hbne, hsub⟩ := M.pumping_lemma hw hlen
  refine ⟨a, b, c, hsplit, by simpa using hab, hbne, ?_⟩
  intro i
  apply hsub
  refine ⟨a ++ (List.replicate i b).flatten, ⟨a, rfl, (List.replicate i b).flatten, ?_, rfl⟩,
    c, rfl, rfl⟩
  exact ⟨List.replicate i b, rfl, fun y hy => by
    simpa using (List.eq_of_mem_replicate hy)⟩

end CS

