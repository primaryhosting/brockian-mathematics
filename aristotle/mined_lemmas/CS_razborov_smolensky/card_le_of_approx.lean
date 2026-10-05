import RequestProject.Circuits
import RequestProject.LowDegree

/-!
# MOD_p is not approximable by low degree functions over a field of characteristic q

This is the second half of Smolensky's argument: if the function `x ↦ ζ^{|x|}`
(`ζ` a primitive `p`-th root of unity in a field `F` of characteristic `q`) agrees
with a function of degree `D` on a set `G` of inputs, then `G` is small.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-- The monomial `∏_{i ∈ S} ζ^{x_i}` in the transformed variables. -/

theorem card_le_of_approx {D : ℕ} (ζ : F) (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    (G : Finset (Fin n → Bool)) (Q : (Fin n → Bool) → F) (hQ : Q ∈ LD F n D)
    (hQG : ∀ x ∈ G, Q x = ζ ^ (count x)) :
    G.card ≤ ∑ i ∈ Finset.range (n / 2 + D + 1), n.choose i := by
  -- every `y`-monomial agrees on `G` with a function of low degree
  have key : ∀ S : Finset (Fin n), ∃ w ∈ LD F n (n / 2 + D), ∀ x ∈ G, yMon ζ S x = w x := by
    intro S
    by_cases hS : S.card ≤ n / 2
    · exact ⟨yMon ζ S, LD_mono (by omega) (yMon_mem_LD ζ S), fun x _ => rfl⟩
    · refine ⟨Q * yMon ζ⁻¹ Sᶜ, ?_, ?_⟩
      · have h1 := mul_mem_LD hQ (yMon_mem_LD (ζ⁻¹) Sᶜ)
        refine LD_mono ?_ h1
        have : Sᶜ.card = n - S.card := by
          rw [Finset.card_compl]
          simp
        have hSn : S.card ≤ n := by
          simpa using Finset.card_le_card (Finset.subset_univ S)
        omega
      · intro x hx
        have hc : (S.filter (fun i => x i = true)).card + (Sᶜ.filter (fun i => x i = true)).card
            = count x := by
          rw [count]
          rw [← Finset.card_union_of_disjoint]
          · congr 1
            ext i
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_compl, Finset.mem_univ,
              true_and]
            tauto
          · refine Finset.disjoint_left.2 fun i hi hi' => ?_
            simp only [Finset.mem_filter, Finset.mem_compl] at hi hi'
            exact hi'.1 hi.1
        simp only [Pi.mul_apply, hQG x hx, yMon_apply]
        rw [← hc, pow_add, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hζ0), mul_one]
  choose w hw hwG using key
  -- the restriction map to `G`
  set R : ((Fin n → Bool) → F) →ₗ[F] ({x // x ∈ G} → F) :=
    LinearMap.funLeft F F (fun (i : {x // x ∈ G}) => (i : Fin n → Bool)) with hR
  have hRsurj : Function.Surjective R :=
    LinearMap.funLeft_surjective_of_injective _ _ _ Subtype.val_injective
  have hmap : Submodule.map R (LD F n (n / 2 + D)) = ⊤ := by
    rw [eq_top_iff]
    have h1 : (⊤ : Submodule F ({x // x ∈ G} → F))
        = Submodule.map R (Submodule.span F (Set.range (yMon ζ (n := n)))) := by
      rw [yMon_span hζ1, Submodule.map_top, LinearMap.range_eq_top.2 hRsurj]
    rw [h1, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro g ⟨-, ⟨S, rfl⟩, rfl⟩
    refine ⟨w S, hw S, ?_⟩
    funext i
    exact (hwG S i.1 i.2).symm
  -- dimension count
  have h2 : Module.finrank F ({x // x ∈ G} → F) ≤ Module.finrank F (LD F n (n / 2 + D)) := by
    have := Submodule.finrank_map_le R (LD F n (n / 2 + D))
    rw [hmap] at this
    simpa using this
  have h3 : Module.finrank F ({x // x ∈ G} → F) = G.card := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  rw [h3] at h2
  exact h2.trans (finrank_LD_le _)

end CS

import Mathlib

/-!
# Binomial estimates

Elementary counting estimates used in the Razborov–Smolensky argument:
a bound on the central binomial coefficient, a bound on the number of
subsets of `Fin (2m)` of size at most `m + D`, and the fact that
exponentials beat polynomials.
-/

namespace CS

open Finset

/-- The central binomial coefficient satisfies `(3m+1) * C(2m,m)^2 ≤ 16^m`
(a sharp form of `C(2m,m) ≤ 4^m / √(3m+1)`). -/
