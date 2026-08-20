/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (it uses only the Lean 4 core library), so that the
required header comment above can literally be the first thing in the file.
-/

namespace CS

/-! ## Counting -/

/-- `HasCard α N` says that the type `α` embeds into `Fin N`; i.e. `α` has at most `N`
elements, so an element of `α` can be stored in `⌈log₂ N⌉` bits. -/

theorem vAt_reset {n d : Nat} (G : RotGraph n d) (D : Nat) (hd : 0 < d) (s : Fin n) {j : Nat}
    (h : j % (D + 1) = D) : vAt G D hd s (j + 1) = s := by
  have hj : (D + 1) * (j / (D + 1)) + j % (D + 1) = j := Nat.div_add_mod j (D + 1)
  have hj' : j + 1 = (D + 1) * (j / (D + 1) + 1) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  have hmod : (j + 1) % (D + 1) = 0 := by rw [hj']; exact Nat.mul_mod_right _ _
  show G.cwalk hd s ((j + 1) / (D + 1)) ((j + 1) % (D + 1)) = s
  rw [hmod]
  rfl

