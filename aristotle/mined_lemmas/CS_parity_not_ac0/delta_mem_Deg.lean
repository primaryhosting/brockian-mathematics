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

lemma delta_mem_Deg (a : Cube n) : delta a ∈ Deg n n := by
  have h : ∀ i : Fin n, (fun x : Cube n => 2 + 2 * sgn (a i) * sgn (x i)) ∈ Deg n 1 := by
    intro i
    have : (fun x : Cube n => 2 + 2 * sgn (a i) * sgn (x i))
        = (fun _ => (2 : ZMod 3)) + (2 * sgn (a i)) • mon ({i} : Finset (Fin n)) := by
      funext x; simp [mon, mul_assoc]
    rw [this]
    exact Submodule.add_mem _ (const_mem_Deg _ _)
      (Submodule.smul_mem _ _ (mon_mem_Deg (by simp)))
  have heq : delta a = ∏ i : Fin n, (fun x : Cube n => 2 + 2 * sgn (a i) * sgn (x i)) := by
    funext x; rw [Finset.prod_apply]; rfl
  rw [heq]
  have := Deg_prod (Finset.univ : Finset (Fin n)) _ 1 (fun i _ => h i)
  simpa [Finset.card_univ] using this

