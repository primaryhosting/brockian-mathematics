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

lemma Cnt_succ_mem (i p : ℕ) (hp : p < P.N) (h : P.vAt p ∈ RS P x i) :
    Cnt P x i (p + 1) = Cnt P x i p + 1 := by
  rw [Cnt, sep_lt_succ_of_mem P x hp h,
    Set.ncard_insert_of_notMem (vAt_not_mem_sep P x hp) (Set.toFinite _)]
  rfl

