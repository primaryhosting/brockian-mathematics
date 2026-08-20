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

theorem safe_sound {pol : Policy} {p : Prog} (h : Safe pol p) :
    ∀ c ∈ p.trace, pol c := by
  induction h with
  | skip => simp
  | use hc => intro c hcp; simpa using (List.mem_singleton.mp hcp) ▸ hc
  | seq _ _ ihp ihq =>
      intro c hc
      simp only [Prog.trace_seq, List.mem_append] at hc
      exact hc.elim (ihp c) (ihq c)
  | ite_true _ ih => intro c hc; exact ih c (by simpa using hc)
  | ite_false _ ih => intro c hc; exact ih c (by simpa using hc)
  | loop_zero => simp [Prog.rep]
  | loop_succ _ ih =>
      intro c hc
      simp only [Prog.trace_loop, Prog.mem_rep] at hc
      exact ih c hc.2

/-- **Completeness of the isolation engine.** Any app whose run-time trace stays
inside the policy admits a certificate. -/
