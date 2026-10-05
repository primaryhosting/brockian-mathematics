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

/-! ## The isolation engine's model

A *proof-carrying app* issues writes to a shared store.  The isolation engine
mediates every write through a `check` predicate: the write is applied only if
the check accepts it.  The intended check is the *capability check*, which
accepts a write exactly when the writing principal holds a capability for the
target address.

We formalise the engine, prove that the capability check is sound (it enforces
the write-integrity policy), and prove the target result: the degenerate engine
whose check is constantly `true` admits a *forge* — a write with no backing
capability that nonetheless mutates the store — so it is unsound. -/

/-- Memory addresses of the shared store. -/
abbrev Addr := Nat

/-- Values held in the shared store. -/
abbrev Val := Nat

/-- Identities that may issue writes. -/
abbrev Principal := Nat

/-- A capability: principal `owner` is permitted to write address `addr`. -/
structure Cap where
  owner : Principal
  addr : Addr
deriving DecidableEq, Repr

/-- A write request: principal `principal` asks to store `val` at `addr`. -/
structure Write where
  principal : Principal
  addr : Addr
  val : Val
deriving DecidableEq, Repr

/-- The shared store. -/
abbrev State := Addr → Val

/-- A write is *authorized* by a capability list when some capability in the
list grants its principal access to its address. -/
def Authorized (caps : List Cap) (w : Write) : Prop :=
  ∃ c ∈ caps, c.owner = w.principal ∧ c.addr = w.addr

/-- Decision procedure for `Authorized`: the engine's intended check. -/
def authorizedB (caps : List Cap) (w : Write) : Bool :=
  caps.any fun c => c.owner == w.principal && c.addr == w.addr

theorem authorizedB_eq_true_iff (caps : List Cap) (w : Write) :
    authorizedB caps w = true ↔ Authorized caps w := by
  simp [authorizedB, Authorized]

/-- Effect of a single (accepted) write on the store. -/
def applyWrite (st : State) (w : Write) : State :=
  fun a => if a = w.addr then w.val else st a

/-- The isolation engine, parameterised by its check.  Each write in the log is
applied if and only if the check accepts it. -/
def run (check : List Cap → Write → Bool) (caps : List Cap) : State → List Write → State
  | st, [] => st
  | st, w :: ws => run check caps (if check caps w then applyWrite st w else st) ws

@[simp] theorem run_nil (check : List Cap → Write → Bool) (caps : List Cap) (st : State) :
    run check caps st [] = st := rfl

@[simp] theorem run_cons (check : List Cap → Write → Bool) (caps : List Cap) (st : State)
    (w : Write) (ws : List Write) :
    run check caps st (w :: ws) =
      run check caps (if check caps w then applyWrite st w else st) ws := rfl

/-- **Write-integrity policy.**  Relative to a starting store `st₀`, a store `st`
is integral when every address whose contents changed is covered by some
capability in `caps`. -/
def Integrity (caps : List Cap) (st₀ st : State) : Prop :=
  ∀ a : Addr, st a ≠ st₀ a → ∃ c ∈ caps, c.addr = a

theorem Integrity.refl (caps : List Cap) (st₀ : State) : Integrity caps st₀ st₀ := by
  intro a ha
  exact absurd rfl ha

/-! ## Soundness of the capability check -/

/-- One accepted write under the capability check preserves integrity. -/
theorem integrity_applyWrite {caps : List Cap} {st₀ st : State} {w : Write}
    (h : Integrity caps st₀ st) (hw : authorizedB caps w = true) :
    Integrity caps st₀ (applyWrite st w) := by
  intro a ha
  by_cases hax : a = w.addr
  · obtain ⟨c, hc, -, hca⟩ := (authorizedB_eq_true_iff caps w).1 hw
    exact ⟨c, hc, by rw [hca, hax]⟩
  · exact h a (by simpa [applyWrite, hax] using ha)

/-- **Soundness.**  The engine driven by the capability check never violates the
write-integrity policy, no matter what log of writes it is fed.
(Proved by induction on the log of writes.) -/
theorem integrity_run_authorizedB (caps : List Cap) (st₀ : State) :
    ∀ (ws : List Write) (st : State), Integrity caps st₀ st →
      Integrity caps st₀ (run authorizedB caps st ws) := by
  intro ws
  induction ws with
  | nil => intro st h; simpa using h
  | cons w ws ih =>
      intro st h
      rw [run_cons]
      by_cases hw : authorizedB caps w = true
      · simpa [hw] using ih _ (integrity_applyWrite h hw)
      · simp only [hw, Bool.false_eq_true, if_false]
        exact ih _ h

/-- Specialisation of soundness to a run started from the initial store. -/
theorem integrity_run_authorizedB_init (caps : List Cap) (st₀ : State) (ws : List Write) :
    Integrity caps st₀ (run authorizedB caps st₀ ws) :=
  integrity_run_authorizedB caps st₀ ws st₀ (Integrity.refl caps st₀)

/-! ## The degenerate check -/

/-- The degenerate check that accepts everything. -/
def trueCheck : List Cap → Write → Bool := fun _ _ => true

@[simp] theorem trueCheck_eq (caps : List Cap) (w : Write) : trueCheck caps w = true := rfl

/-- Under the constantly-true check the engine simply applies every write in the
log, capabilities notwithstanding.  (Proved by induction on the log.) -/
theorem run_trueCheck (caps : List Cap) :
    ∀ (ws : List Write) (st : State),
      run trueCheck caps st ws = ws.foldl applyWrite st := by
  intro ws
  induction ws with
  | nil => intro st; simp
  | cons w ws ih => intro st; simp [ih]

/-! ## The forge -/

/-- A forged write: principal `0` writing `1` to address `0`. -/
def forgedWrite : Write := ⟨0, 0, 1⟩

/-- The all-zero store. -/
def zeroState : State := fun _ => 0

theorem forgedWrite_not_authorized : ¬ Authorized [] forgedWrite := by
  rintro ⟨c, hc, -⟩
  exact absurd hc List.not_mem_nil

/-- **Target.**  An isolation engine whose check is constantly `true` admits a
forge: there is a capability list, an initial store, and a log consisting solely
of *unauthorized* writes, such that the engine accepts them all and the resulting
store violates the write-integrity policy.  Hence such an engine is unsound —
in contrast with `integrity_run_authorizedB_init` for the capability check. -/
theorem with_check_true_admits_forge :
    ∃ (caps : List Cap) (st₀ : State) (ws : List Write),
      (∀ w ∈ ws, ¬ Authorized caps w) ∧
      ¬ Integrity caps st₀ (run trueCheck caps st₀ ws) := by
  refine ⟨[], zeroState, [forgedWrite], ?_, ?_⟩
  · intro w hw
    rw [List.mem_singleton.1 hw]
    exact forgedWrite_not_authorized
  · intro hI
    obtain ⟨c, hc, -⟩ := hI 0 (by
      simp [applyWrite, forgedWrite, zeroState])
    exact absurd hc List.not_mem_nil

end WriteIntegrity
end PCA

#print axioms PCA.WriteIntegrity.with_check_true_admits_forge
#print axioms PCA.WriteIntegrity.integrity_run_authorizedB_init

