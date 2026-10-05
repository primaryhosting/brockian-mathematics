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

lemma yMon_mem_LD (ζ : F) (S : Finset (Fin n)) : yMon ζ S ∈ LD F n S.card := by
  have h : ∀ i ∈ S, (fun x : Fin n → Bool => 1 + (ζ - 1) * bv F (x i)) ∈ LD F n 1 := by
    intro i _
    refine Submodule.add_mem _ (one_mem_LD 1) ?_
    have : (fun x : Fin n → Bool => (ζ - 1) * bv F (x i))
        = (ζ - 1) • (fun x : Fin n → Bool => bv F (x i)) := by
      funext x; simp [smul_eq_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (coord_mem_LD i 1 le_rfl)
  have h2 := prod_mem_LD S (fun i => (fun x : Fin n → Bool => 1 + (ζ - 1) * bv F (x i)))
    (fun _ => 1) h
  have heq : yMon ζ S = ∏ i ∈ S, (fun x : Fin n → Bool => 1 + (ζ - 1) * bv F (x i)) := by
    funext x; simp [yMon, Finset.prod_apply]
  rw [heq]
  simpa using h2

/-- The `y`-monomials span all functions on the cube. -/
