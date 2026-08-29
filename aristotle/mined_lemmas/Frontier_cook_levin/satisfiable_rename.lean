/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Frontier

/-! ## Propositional formulas in conjunctive normal form -/

/-- A literal over a type `V` of variables: a variable together with a polarity. -/
structure Lit (V : Type) where
  var : V
  pol : Bool
deriving DecidableEq

/-- A clause is a disjunction of literals. -/
abbrev Clause (V : Type) := List (Lit V)

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF (V : Type) := List (Clause V)

/-- Value of a literal under an assignment. -/

theorem satisfiable_rename {V W : Type} {f : V → W} (hf : Function.Injective f) (φ : CNF V) :
    Satisfiable (CNF.rename f φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨fun v => b (f v), by rwa [CNF.eval_rename (a := fun v => b (f v)) (fun _ => rfl)] at hb⟩
  · rintro ⟨a, ha⟩
    classical
    refine ⟨fun w => if h : ∃ v, f v = w then a h.choose else false, ?_⟩
    have key : ∀ v : V, (if h : ∃ v', f v' = f v then a h.choose else false) = a v := by
      intro v
      have hex : ∃ v', f v' = f v := ⟨v, rfl⟩
      rw [dif_pos hex]
      have : hex.choose = v := hf hex.choose_spec
      rw [this]
    rwa [CNF.eval_rename key]

/-! ## Turing machines -/

/-- Direction of a head move. -/
inductive Dir where
  | L : Dir
  | R : Dir
  | S : Dir
deriving DecidableEq

/-- Tape symbols: `none` is the blank symbol. -/
abbrev Sym := Option Bool

/-- A deterministic one-tape Turing machine with `n` states, working over the
tape alphabet `Sym = Option Bool`. -/
structure TM (n : Nat) where
  /-- Transition function: new state, symbol written, direction of head move. -/
  step : Fin n → Sym → Fin n × Sym × Dir
  /-- Initial state. -/
  start : Fin n
  /-- Accepting state. -/
  accept : Fin n

/-- A configuration: current state, tape contents (indexed by `Nat`), head position. -/
structure Cfg (n : Nat) where
  /-- Current state. -/
  state : Fin n
  /-- Tape contents. -/
  tape : Nat → Sym
  /-- Head position. -/
  head : Nat

/-- One step of the machine.  A left move at position `0` leaves the head at `0`. -/
