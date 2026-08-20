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

lemma machine_accepts (n : ℕ) (x : Fin n → Bool) :
    (machine n).Accepts x ↔ ∃ i, x i = true := by
  constructor
  · rintro ⟨v, hv, hreach⟩
    have hv' : v = Sum.inr (Sum.inr ()) := hv
    rcases reach_cases n x v hreach with h | ⟨i, h⟩ | h
    · rw [hv'] at h; exact absurd h (by simp)
    · rw [hv'] at h; exact absurd h (by simp)
    · exact h
  · rintro ⟨i, hi⟩
    refine ⟨Sum.inr (Sum.inr ()), rfl, ?_⟩
    refine Relation.ReflTransGen.head (b := Sum.inr (Sum.inl i)) ?_
      (Relation.ReflTransGen.single ?_)
    · show (Guard.always : Guard n).eval x = true
      rfl
    · show (Guard.bit i true).eval x = true
      simp [Guard.eval, hi]

end OrLang

/-- The language `OR` (some input bit is `1`) lies in `NL`; in particular `NL` is not
a degenerate class. -/
