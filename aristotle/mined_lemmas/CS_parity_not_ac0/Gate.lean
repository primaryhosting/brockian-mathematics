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

lemma Gate.eval_congr {n m : ℕ} (x : Cube n) (v w : Fin m → Bool) (g : Gate n m)
    (h : ∀ j ∈ g.refs, v j = w j) : g.eval x v = g.eval x w := by
  cases g with
  | const b => rfl
  | var i => rfl
  | not j => simp [Gate.eval, h j (by simp [Gate.refs])]
  | and s =>
      simp only [Gate.eval]
      congr 1
      exact propext ⟨fun H j hj => (h j hj) ▸ H j hj, fun H j hj => (h j hj).symm ▸ H j hj⟩
  | or s =>
      simp only [Gate.eval]
      congr 1
      refine propext ⟨fun ⟨j, hj, H⟩ => ⟨j, hj, (h j hj) ▸ H⟩,
        fun ⟨j, hj, H⟩ => ⟨j, hj, (h j hj).symm ▸ H⟩⟩

/-- A Boolean circuit with `n` inputs: `size` gates, topologically ordered. -/
structure Circuit (n : ℕ) where
  size : ℕ
  gate : Fin size → Gate n size
  out : Fin size
  wf : ∀ i j, j ∈ (gate i).refs → (j : ℕ) < (i : ℕ)

variable {n : ℕ}

/-- `v` is *the* vector of gate values of `c` on input `x`. -/
