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
def rep : Nat → List Cap → List Cap
  | 0, _ => []
  | n + 1, t => t ++ rep n t

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
def trace : Prog → List Cap
  | .skip => []
  | .use c => [c]
  | .seq p q => trace p ++ trace q
  | .ite b p q => if b then trace p else trace q
  | .loop n p => rep n (trace p)

@[simp] theorem trace_skip : trace .skip = [] := rfl
@[simp] theorem trace_use (c : Cap) : trace (.use c) = [c] := rfl
@[simp] theorem trace_seq (p q : Prog) : trace (.seq p q) = trace p ++ trace q := rfl
@[simp] theorem trace_ite (b : Bool) (p q : Prog) :
    trace (.ite b p q) = if b then trace p else trace q := rfl
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
def ProvedClean (pol : Policy) (p : Prog) : Prop := Safe pol p

/-- An app *escapes* the sandbox when its run-time trace exercises a capability
that the policy does not permit. -/
def Escapes (pol : Policy) (p : Prog) : Prop := ∃ c ∈ p.trace, ¬ pol c

/-- **Soundness of the isolation engine.** A certified app only exercises
capabilities allowed by the policy. -/
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
theorem safe_iff_not_escapes {pol : Policy} {p : Prog} :
    Safe pol p ↔ ¬ Escapes pol p := by
  constructor
  · rintro h ⟨c, hc, hnc⟩
    exact hnc (safe_sound h c hc)
  · intro h
    exact safe_complete fun c hc => Classical.byContradiction fun hnc => h ⟨c, hc, hnc⟩

/-- **Main theorem.** No app is simultaneously proved clean by the isolation engine
and able to escape its sandbox. -/
theorem no_clean_proved_with_escape (pol : Policy) (p : Prog) :
    ¬ (ProvedClean pol p ∧ Escapes pol p) := by
  rintro ⟨hsafe, hesc⟩
  exact (safe_iff_not_escapes.mp hsafe) hesc

/-! ### Non-vacuity: both sides of the dichotomy are inhabited. -/

/-- The policy permitting exactly capabilities `0` and `1`. -/
def demoPolicy : Policy := fun c => c = 0 ∨ c = 1

/-- A concrete app that the engine certifies. -/
example : ProvedClean demoPolicy (.seq (.use 0) (.loop 3 (.use 1))) :=
  Safe.seq (Safe.use (Or.inl rfl)) (Safe.loop_succ (Safe.use (Or.inr rfl)))

/-- A concrete app that escapes the sandbox. -/
example : Escapes demoPolicy (.seq (.use 0) (.use 2)) :=
  ⟨2, by simp, by simp [demoPolicy]⟩

/-- Hence that app is not certified by the engine. -/
example : ¬ ProvedClean demoPolicy (.seq (.use 0) (.use 2)) := fun h =>
  no_clean_proved_with_escape _ _ ⟨h, ⟨2, by simp, by simp [demoPolicy]⟩⟩

end PCA.Isolation

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

