import RequestProject.Machine

/-!
# The inductive counting construction

Given a nondeterministic branching program we build, by Immerman and Szelepcsényi's
inductive counting method, a nondeterministic branching program of polynomially larger
size accepting exactly the complementary language.
-/

namespace CS

namespace Compl

variable {n : ℕ} (P : Setup n)

/-! ### The invariant -/

variable (x : Fin n → Bool)

/-- The set of configurations of the original machine reachable in at most `i` steps. -/

lemma Rle_stable {i : ℕ} (h : Rle E st (i + 1) = Rle E st i) :
    ∀ j, i ≤ j → Rle E st j = Rle E st i := by
  intro j hj
  induction j with
  | zero => simp [Nat.le_zero.mp hj]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · have hij : i ≤ j := Nat.lt_succ_iff.mp hlt
        have hj' : Rle E st j = Rle E st i := ih hij
        rw [Rle_succ, hj']
        rw [Rle_succ] at h
        exact h
      · have : i = j + 1 := le_antisymm hj hge
        subst this; rfl

