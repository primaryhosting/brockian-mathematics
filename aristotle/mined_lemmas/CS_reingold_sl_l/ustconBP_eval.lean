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

theorem ustconBP_eval [NeZero D] (hk : 0 < k) (nbr : Fin n → Fin D → Fin n) (s t : Fin n) :
    (ustconBP n D k s t).eval (fun q => nbr q.1 q.2) = true ↔ ReachWithin nbr s t k := by
  have h := ustconBP_run (n := n) (D := D) (k := k) hk nbr s t (D ^ k * k)
  have hlen : (ustconBP n D k s t).length = D ^ k * k := rfl
  rw [BP.eval, hlen]
  refine ⟨fun hacc => ?_, fun hreach => ?_⟩
  · have := h.2.1 hacc
    rcases this with hst | ⟨l, hl, hw⟩
    · exact ⟨fun _ => dig D 0 0, 0, Nat.zero_le _, hst⟩
    · exact ⟨dig D (l / k), l % k + 1, Nat.succ_le_of_lt (Nat.mod_lt _ hk), hw⟩
  · refine h.2.2 ?_
    obtain ⟨w, j, hj, hw⟩ := hreach
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact Or.inl hw
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      have hmk : m < k := by omega
      set i : ℕ := ((finFunctionFinEquiv (fun x : Fin k => w x) : Fin (D ^ k)) : ℕ) with hi
      have hik : i < D ^ k := (finFunctionFinEquiv (fun x : Fin k => w x)).isLt
      refine Or.inr ⟨k * i + m, ?_, ?_⟩
      · calc k * i + m < k * i + k := by omega
          _ = k * (i + 1) := by ring
          _ ≤ k * D ^ k := Nat.mul_le_mul_left _ hik
          _ = D ^ k * k := Nat.mul_comm _ _
      · have hdiv : (k * i + m) / k = i := by
          rw [Nat.mul_add_div hk, Nat.div_eq_of_lt hmk, Nat.add_zero]
        have hmod : (k * i + m) % k = m := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hmk]
        rw [hdiv, hmod]
        rw [← hw]
        refine walk_congr _ _ _ _ _ (fun x hx => ?_)
        exact dig_of_finFunctionFinEquiv (k := k) w x (by omega)

