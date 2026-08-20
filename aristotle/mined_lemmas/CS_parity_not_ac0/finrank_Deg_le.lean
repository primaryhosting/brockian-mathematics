import RequestProject.OrApprox

/-!
# Approximating a whole `AC⁰` circuit by a low degree polynomial

Gate by gate (in topological order) we replace each gate by a low degree
function over `ZMod 3`, accumulating an exceptional set of inputs.  A circuit of
depth `d` with `s` gates is approximated by a function of degree `(2ℓ)^d`
outside a set of at most `s · 2^{n-ℓ}` inputs.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- The vector of gate values of a circuit on a given input. -/

lemma finrank_Deg_le (n K : ℕ) :
    Module.finrank (ZMod 3) (Deg n K) ≤ ∑ k ∈ Finset.range (K + 1), n.choose k := by
  classical
  set gen : Finset (Cube n → ZMod 3) :=
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ K)).image mon with hgen
  have hset : (gen : Set (Cube n → ZMod 3)) = {f | ∃ S : Finset (Fin n), S.card ≤ K ∧ f = mon S} := by
    ext f
    simp only [hgen, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, Set.mem_setOf_eq]
    constructor
    · rintro ⟨S, hS, rfl⟩; exact ⟨S, hS, rfl⟩
    · rintro ⟨S, hS, rfl⟩; exact ⟨S, hS, rfl⟩
  have hspan : Deg n K = Submodule.span (ZMod 3) (gen : Set (Cube n → ZMod 3)) := by
    rw [Deg, hset]
  rw [hspan]
  refine le_trans (finrank_span_finset_le_card gen) ?_
  refine le_trans (Finset.card_image_le) (card_filter_card_le n K)

/-- **Smolensky's dimension bound.** -/
