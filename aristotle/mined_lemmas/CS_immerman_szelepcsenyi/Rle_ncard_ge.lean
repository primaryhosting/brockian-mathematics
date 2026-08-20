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

lemma Rle_ncard_ge [Fintype V] {i : ℕ} (h : ∀ k, k < i → Rle E st k ≠ Rle E st (k + 1)) :
    i + 1 ≤ (Rle E st i).ncard := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hih : i + 1 ≤ (Rle E st i).ncard := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
      have hss : Rle E st i ⊂ Rle E st (i + 1) :=
        ssubset_of_subset_of_ne (Rle_subset_succ E st i) (h i (Nat.lt_succ_self i))
      have := Set.ncard_lt_ncard hss (Set.toFinite _)
      omega

/-- Every vertex reachable from `st` is reachable by a walk of length at most
`card V - 1`. -/
