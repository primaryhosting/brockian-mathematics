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

theorem vAt_advance {n d : Nat} (G : RotGraph n d) (D : Nat) (hd : 0 < d) (s : Fin n) {j : Nat}
    (h : j % (D + 1) ≠ D) :
    vAt G D hd s (j + 1) =
      G.step1 (vAt G D hd s j) (digitF hd (j / (D + 1)) (j % (D + 1))) := by
  have hm : 0 < D + 1 := Nat.succ_pos D
  have hlt : j % (D + 1) < D + 1 := Nat.mod_lt _ hm
  have hj : (D + 1) * (j / (D + 1)) + j % (D + 1) = j := Nat.div_add_mod j (D + 1)
  have hj' : j + 1 = (j % (D + 1) + 1) + (D + 1) * (j / (D + 1)) := by omega
  have hmod : (j + 1) % (D + 1) = j % (D + 1) + 1 := by
    rw [hj', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hdiv : (j + 1) / (D + 1) = j / (D + 1) := by
    rw [hj', Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  show G.cwalk hd s ((j + 1) / (D + 1)) ((j + 1) % (D + 1)) = _
  rw [hmod, hdiv]
  rfl

/-- The invariant maintained by the machine along its run. -/
