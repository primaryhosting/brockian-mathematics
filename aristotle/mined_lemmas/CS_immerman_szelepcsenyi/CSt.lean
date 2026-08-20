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

def CSt.equivProd (N : ℕ) (V : Type) :
    CSt N V ≃ (Fin 5 × Fin (N + 1) × Fin (N + 1) × Fin (N + 1) × Fin (N + 1) × Fin (N + 1) ×
      Fin (N + 1) × Fin (N + 1) × V × Bool) where
  toFun s := (s.pc, s.i, s.r, s.r2, s.v, s.c, s.u, s.j, s.w, s.fnd)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
    t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2⟩
  left_inv s := by cases s; rfl
  right_inv t := rfl

instance (N : ℕ) (V : Type) [Fintype V] : Fintype (CSt N V) :=
  Fintype.ofEquiv _ (CSt.equivProd N V).symm

