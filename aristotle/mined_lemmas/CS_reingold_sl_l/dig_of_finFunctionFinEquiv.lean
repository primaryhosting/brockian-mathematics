/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-! ## Graphs presented by neighbour maps -/

variable {n D k : ℕ}

/-- `walk nbr v w j` is the vertex reached from `v` after following the first `j`
directions of the direction sequence `w` in the `D`-regular graph given by the
neighbour map `nbr`. -/

theorem dig_of_finFunctionFinEquiv [NeZero D] (w : ℕ → Fin D) (b : ℕ) (hb : b < k) :
    dig D ((finFunctionFinEquiv (fun i : Fin k => w i) : Fin (D ^ k)) : ℕ) b = w b := by
  have h : ((finFunctionFinEquiv (fun i : Fin k => w i) : Fin (D ^ k)) : ℕ)
      / D ^ (⟨b, hb⟩ : Fin k).1 % D = (w b : ℕ) :=
    congrArg Fin.val
      (congrFun (finFunctionFinEquiv.symm_apply_apply (fun i : Fin k => w i)) ⟨b, hb⟩)
  exact Fin.ext h

/-- **Correctness of the program.**  `ustconBP n D k s t` accepts the `D`-regular graph
`nbr` exactly when `t` can be reached from `s` by a walk of length at most `k`. -/
