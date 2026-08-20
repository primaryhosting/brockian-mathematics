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

lemma cNBP_accepts (P : Setup n) (x : Fin n → Bool) :
    (cNBP P).Accepts x ↔ ¬ ∃ y, P.acc y ∧ Relation.ReflTransGen (P.step x) P.st y := by
  constructor
  · rintro ⟨s, hs4, hreach⟩ ⟨y, hacc, hy⟩
    have hreach' : Relation.ReflTransGen (cstep P x) (cstart P) s :=
      hreach.mono (fun a b h => (cedg_eval P x a b).mp h)
    exact sound P x hreach' hs4 y hy hacc
  · intro hno
    push_neg at hno
    obtain ⟨t, htpc, ht⟩ := complete P x (fun y hy hacc => hno y hacc hy)
    exact ⟨t, htpc, ht.mono (fun a b h => (cedg_eval P x a b).mpr h)⟩

end Compl

/-- The setup associated with a nondeterministic branching program. -/
