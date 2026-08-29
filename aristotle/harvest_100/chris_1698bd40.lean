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

/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA
namespace WriteIntegrity

/-! ## The isolation engine's write model -/

/-- Principals (subjects) of the isolation engine. -/
abbrev Principal := Nat

/-- Memory addresses of the isolated store. -/
abbrev Addr := Nat

/-- Values that can be stored. -/
abbrev Val := Nat

/-- A write request: a principal asks to store `val` at `addr`. -/
structure Write where
  principal : Principal
  addr : Addr
  val : Val
deriving DecidableEq, Repr

/-- The state of the isolated store. -/
abbrev Mem := Addr → Val

/-- Point update of the store. -/
def store (m : Mem) (a : Addr) (v : Val) : Mem :=
  fun x => if x = a then v else m x

@[simp] theorem store_self (m : Mem) (a : Addr) (v : Val) : store m a v a = v := by
  simp [store]

/-- An access-control policy assigns to each address its owning principal. -/
structure Policy where
  owner : Addr → Principal

/-- A write is *authorized* by the policy when its issuer owns the target address. -/
def Policy.Authorized (P : Policy) (w : Write) : Prop :=
  P.owner w.addr = w.principal

/-- A write-integrity engine is determined by the check it runs on each request. -/
structure Engine where
  check : Write → Bool

/-- One step of the engine: an admitted write updates memory and is appended to the
audit log; a rejected write leaves the state untouched. -/
def Engine.step (E : Engine) (s : Mem × List Write) (w : Write) : Mem × List Write :=
  if E.check w then (store s.1 w.addr w.val, s.2 ++ [w]) else s

/-- Running the engine on a trace of requests, starting from memory `m` and an empty log. -/
def Engine.run (E : Engine) (m : Mem) (ws : List Write) : Mem × List Write :=
  ws.foldl E.step (m, [])

/-- The unchecked (reference) semantics: every request is applied. -/
def applyAll (m : Mem) (ws : List Write) : Mem :=
  ws.foldl (fun m w => store m w.addr w.val) m

/-- **Write integrity**: an engine is sound for a policy when every write it admits
(i.e. every write appearing in the audit log of some run) is authorized. -/
def Sound (E : Engine) (P : Policy) : Prop :=
  ∀ (m : Mem) (ws : List Write) (w : Write), w ∈ (E.run m ws).2 → P.Authorized w

/-- The degenerate engine whose check is constantly `true`. -/
def trivialEngine : Engine := ⟨fun _ => true⟩

/-! ## Behaviour of the constantly-true check -/

/-- Generalized form of a run of the constantly-true engine, proved by structural
induction on the trace: every request is admitted, so the audit log is the whole trace
and the memory is the unchecked fold. -/
theorem trivial_foldl (ws : List Write) :
    ∀ (m : Mem) (log : List Write),
      ws.foldl trivialEngine.step (m, log) = (applyAll m ws, log ++ ws) := by
  induction ws with
  | nil => intro m log; simp [applyAll]
  | cons w ws ih =>
    intro m log
    have hstep : trivialEngine.step (m, log) w
        = (store m w.addr w.val, log ++ [w]) := by
      simp [Engine.step, trivialEngine]
    simp only [List.foldl_cons, hstep, ih, applyAll, List.append_assoc,
      List.cons_append, List.nil_append]

/-- With the constantly-true check, the audit log of a run is exactly the input trace. -/
theorem trivial_log (m : Mem) (ws : List Write) :
    (trivialEngine.run m ws).2 = ws := by
  simp [Engine.run, trivial_foldl]

/-- With the constantly-true check, the resulting memory is the unchecked fold. -/
theorem trivial_mem (m : Mem) (ws : List Write) :
    (trivialEngine.run m ws).1 = applyAll m ws := by
  simp [Engine.run, trivial_foldl]

/-! ## The forgery -/

/-- A concrete forged request against address `0`: it is issued by a principal that is
not the owner of address `0`, and it writes a value different from the current one. -/
def forgedWrite (P : Policy) (m : Mem) : Write :=
  { principal := P.owner 0 + 1, addr := 0, val := m 0 + 1 }

theorem forgedWrite_not_authorized (P : Policy) (m : Mem) :
    ¬ P.Authorized (forgedWrite P m) := by
  simp [Policy.Authorized, forgedWrite]

/-- **Main result.** An engine whose check is constantly `true` provides no write
integrity: for every policy and every starting memory there is a nonempty trace
consisting solely of unauthorized (forged) requests which the engine nevertheless
admits in full, thereby tampering with memory. Consequently such an engine is unsound
for every policy. -/
theorem with_check_true_admits_forge (P : Policy) (m : Mem) :
    ∃ ws : List Write,
      ws ≠ [] ∧
      (∀ w ∈ ws, ¬ P.Authorized w) ∧
      (trivialEngine.run m ws).2 = ws ∧
      (trivialEngine.run m ws).1 ≠ m ∧
      ¬ Sound trivialEngine P := by
  refine ⟨[forgedWrite P m], by simp, ?_, trivial_log m _, ?_, ?_⟩
  · intro w hw
    simp only [List.mem_singleton] at hw
    subst hw
    exact forgedWrite_not_authorized P m
  · rw [trivial_mem]
    intro h
    have h0 : applyAll m [forgedWrite P m] 0 = m 0 := by rw [h]
    simp [applyAll, forgedWrite] at h0
  · intro hsound
    have hmem : forgedWrite P m ∈ (trivialEngine.run m [forgedWrite P m]).2 := by
      rw [trivial_log]; simp
    exact forgedWrite_not_authorized P m (hsound m _ _ hmem)

end WriteIntegrity
end PCA

