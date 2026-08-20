/-!
# No Clean Proved With Escape
Category: Proof-Carrying Apps
Target: PCA.Isolation.no_clean_proved_with_escape
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Isolation

/-- Capabilities an app may exercise (e.g. file handles, sockets, syscalls). -/
abbrev Cap : Type := Nat

/-- A sandbox policy is the predicate describing which capabilities the
isolation engine permits. -/
abbrev Policy : Type := Cap → Prop

/-- A minimal app language for the isolation engine: capability uses, sequencing,
resolved conditionals, and bounded loops. -/
inductive Prog : Type
  | skip : Prog
  | use : Cap → Prog
  | seq : Prog → Prog → Prog
  | ite : Bool → Prog → Prog → Prog
  | loop : Nat → Prog → Prog
  deriving DecidableEq

namespace Prog

/-- `rep n t` is `t` repeated `n` times, the trace of a bounded loop body. -/

@[simp] theorem mem_rep {n : Nat} {t : List Cap} {c : Cap} :
    c ∈ rep n t ↔ 0 < n ∧ c ∈ t := by
  induction n with
  | zero => simp [rep]
  | succ n ih =>
      simp only [rep, List.mem_append, ih, Nat.succ_pos, true_and]
      constructor
      · rintro (h | ⟨-, h⟩) <;> exact h
      · exact fun h => Or.inl h

/-- The dynamic semantics: the list of capabilities actually exercised at run time. -/
