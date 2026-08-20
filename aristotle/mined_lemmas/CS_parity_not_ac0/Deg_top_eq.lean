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

lemma Deg_top_eq : Deg n n = ⊤ := by
  refine eq_top_iff.mpr (fun f _ => ?_)
  have hf : f = ∑ a : Cube n, f a • delta a := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, delta_apply, smul_eq_mul]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]; ring
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [hf]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (delta_mem_Deg a))

/-- The full monomial computes the parity of the input in the `±1` encoding. -/
