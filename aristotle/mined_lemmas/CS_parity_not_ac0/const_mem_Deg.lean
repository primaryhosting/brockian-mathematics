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

lemma const_mem_Deg (a : ZMod 3) (D : ℕ) : (fun _ => a : Cube n → ZMod 3) ∈ Deg n D := by
  have : (fun _ => a : Cube n → ZMod 3) = a • (1 : Cube n → ZMod 3) := by
    funext x; simp
  rw [this]
  exact Submodule.smul_mem _ _ (one_mem_Deg D)

