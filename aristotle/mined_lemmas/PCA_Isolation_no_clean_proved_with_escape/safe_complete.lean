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

theorem safe_complete {pol : Policy} {p : Prog} (h : ∀ c ∈ p.trace, pol c) :
    Safe pol p := by
  induction p with
  | skip => exact .skip
  | use c => exact .use (h c (by simp))
  | seq p q ihp ihq =>
      refine .seq (ihp ?_) (ihq ?_) <;> intro c hc <;> exact h c (by simp [hc])
  | ite b p q ihp ihq =>
      cases b with
      | true => exact .ite_true (ihp (fun c hc => h c (by simpa using hc)))
      | false => exact .ite_false (ihq (fun c hc => h c (by simpa using hc)))
  | loop n p ih =>
      cases n with
      | zero => exact .loop_zero
      | succ n =>
          exact .loop_succ (ih (fun c hc => h c (by simp [hc])))

/-- The engine's certificate is exactly the absence of a sandbox escape. -/
