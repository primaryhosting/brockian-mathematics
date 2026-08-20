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

lemma not_acc_of_mem_RS (hno : ∀ y, Relation.ReflTransGen (P.step x) P.st y → ¬ P.acc y)
    (i : ℕ) (y : P.V) (hy : y ∈ RS P x i) : ¬ P.acc y :=
  hno y (Rle_subset_reach (P.step x) P.st hy)

