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

lemma sound {s : CSt P.N P.V} (h : Relation.ReflTransGen (cstep P x) (cstart P) s)
    (hpc : s.pc = 4) : ∀ y, Relation.ReflTransGen (P.step x) P.st y → ¬ P.acc y := by
  have hInv : Inv P x s := inv_of_reach P x h
  intro y hy hacc
  have hcert := hInv.2.2.2.2 hpc
  have hmem : y ∈ Rle (P.step x) P.st (Fintype.card P.V - 1) :=
    reach_mem_Rle_card (P.step x) P.st hy
  rw [P.card_V] at hmem
  exact hcert (P.N - 1) (by have := P.hN; omega) y hmem hacc

