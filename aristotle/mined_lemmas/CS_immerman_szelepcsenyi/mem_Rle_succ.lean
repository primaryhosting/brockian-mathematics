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

lemma mem_Rle_succ {i : ℕ} {z : V} :
    z ∈ Rle E st (i + 1) ↔ (z ∈ Rle E st i ∨ ∃ y ∈ Rle E st i, E y z) := Iff.rfl

