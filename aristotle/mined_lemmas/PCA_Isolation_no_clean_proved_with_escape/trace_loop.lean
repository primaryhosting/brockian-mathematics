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

@[simp] theorem trace_loop (n : Nat) (p : Prog) : trace (.loop n p) = rep n (trace p) := rfl

end Prog

/-- The proof certificate checked by the isolation engine: a structural derivation
that every capability the app can exercise is permitted by the policy. -/
inductive Safe (pol : Policy) : Prog → Prop
  | skip : Safe pol .skip
  | use {c : Cap} : pol c → Safe pol (.use c)
  | seq {p q : Prog} : Safe pol p → Safe pol q → Safe pol (.seq p q)
  | ite_true {p q : Prog} : Safe pol p → Safe pol (.ite true p q)
  | ite_false {p q : Prog} : Safe pol q → Safe pol (.ite false p q)
  | loop_zero {p : Prog} : Safe pol (.loop 0 p)
  | loop_succ {n : Nat} {p : Prog} : Safe pol p → Safe pol (.loop (n + 1) p)

/-- An app is *proved clean* for a policy when the engine holds a `Safe` certificate. -/
