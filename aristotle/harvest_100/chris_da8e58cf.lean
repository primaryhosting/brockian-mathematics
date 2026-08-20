/-
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4.28 does not allow a module docstring before the import block, so this header
is a plain block comment; the text is otherwise verbatim.)
-/

import Mathlib
import RequestProject.CookLevin.Sat
import RequestProject.CookLevin.Machine
import RequestProject.CookLevin.Tableau
import RequestProject.CookLevin.Forward
import RequestProject.CookLevin.Backward
import RequestProject.CookLevin.Size
import RequestProject.CookLevin.Sanity
import RequestProject.CookLevin.Certificate

/-!
## The Cook–Levin theorem

`Frontier.cook_levin` states that SAT is `NP`-hard: every language `L` in `NP` is reduced to
`SATLang`, the set of satisfiable CNF formulas over `ℕ`, by the explicit computable map
`Frontier.reduction`, whose output is of polynomial size.

The complexity class `NP` is modelled by single-tape nondeterministic Turing machines
(`Frontier.NTM`) with a polynomial time bound (`Frontier.InNP`), and the reduction is the
classical *tableau* construction: `Frontier.tableau M x T` is a CNF formula whose satisfying
assignments are exactly the accepting computations of `M` on `x` of length `T`
(`Frontier.tableau_satisfiable_iff`).

### Sources and scope

* Mathlib (at the version pinned by this project) contains no complexity theory: there is no
  definition of `P`, `NP`, of polynomial-time reductions, or of SAT, and no Cook–Levin
  statement.  Everything below is therefore developed from scratch, except for the CNF
  datatype `Std.Sat.CNF` and its relabelling API, which come from the Lean core library.
* What is proved is the hard half of the Cook–Levin theorem, `NP`-hardness of SAT, for
  many-one reductions that are computable Lean functions of polynomially bounded output
  size.  Two ingredients of the textbook statement are *not* formalised here: that the
  reduction runs in polynomial *time* (this project fixes no cost model for computing the
  reduction itself), and the easy half `SAT ∈ NP` (which would require programming and
  verifying a nondeterministic Turing machine that parses and evaluates encoded formulas).
  `Frontier.satisfiable_iff_exists_certificate` records the certificate characterisation of
  satisfiability that underlies the easy half.
-/

namespace Frontier

open Std.Sat

/-! ### Encoding the tableau variables by natural numbers -/

/-- Numerical code of a tape symbol. -/
def symCode : Sym → ℕ
  | none => 0
  | some false => 1
  | some true => 2

theorem symCode_injective : Function.Injective symCode := by decide

/-- An injective encoding of the tableau variables by natural numbers. -/
def encTVar : TVar → ℕ
  | TVar.st t q => 4 * Nat.pair t q
  | TVar.hd t i => 4 * Nat.pair t i + 1
  | TVar.cell t i a => 4 * Nat.pair (Nat.pair t i) (symCode a) + 2
  | TVar.mv t j => 4 * Nat.pair t j + 3

theorem encTVar_injective : Function.Injective encTVar := by
  intro u v huv
  cases u <;> cases v <;> simp only [encTVar] at huv
  case st.st t q t' q' =>
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 (show Nat.pair t q = Nat.pair t' q' by omega)
    rfl
  case hd.hd t i t' i' =>
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 (show Nat.pair t i = Nat.pair t' i' by omega)
    rfl
  case cell.cell t i a t' i' a' =>
    obtain ⟨hp, hs⟩ := Nat.pair_eq_pair.1 (show Nat.pair (Nat.pair t i) (symCode a) =
      Nat.pair (Nat.pair t' i') (symCode a') by omega)
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 hp
    rw [symCode_injective hs]
  case mv.mv t j t' j' =>
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 (show Nat.pair t j = Nat.pair t' j' by omega)
    rfl
  all_goals omega

/-! ### Correctness of the tableau -/

variable {M : NTM} {x : List Bool} {T : ℕ}

/-- **Correctness of the Cook–Levin tableau.**  The formula `tableau M x T` is satisfiable
if and only if the nondeterministic machine `M` accepts the input `x` within `T` steps. -/
theorem tableau_satisfiable_iff : Satisfiable (tableau M x T) ↔ M.Accepts x T :=
  ⟨accepts_of_satisfiable_tableau, satisfiable_tableau_of_accepts⟩

/-- The reduction of a polynomially time-bounded machine to SAT: the tableau formula,
with its variables encoded as natural numbers. -/
def reduction (M : NTM) (c k : ℕ) (x : List Bool) : CNF ℕ :=
  CNF.relabel encTVar (tableau M x (c * (x.length + 1) ^ k))

theorem reduction_satisfiable_iff (M : NTM) (c k : ℕ) (x : List Bool) :
    Satisfiable (reduction M c k x) ↔ M.Accepts x (c * (x.length + 1) ^ k) := by
  rw [reduction, satisfiable_relabel_iff encTVar_injective, tableau_satisfiable_iff]

theorem length_reduction_le (M : NTM) (c k : ℕ) (x : List Bool) :
    (reduction M c k x).length ≤
      (M.numStates ^ 2 + 5 * M.transList.length + 22) * (c + 1) ^ 3 *
        (x.length + 1) ^ (3 * k) := by
  have h1 : (reduction M c k x).length = (tableau M x (c * (x.length + 1) ^ k)).length := by
    simp [reduction, CNF.relabel]
  have h2 := length_tableau_le M x (c * (x.length + 1) ^ k)
  have h3 : c * (x.length + 1) ^ k + 1 ≤ (c + 1) * (x.length + 1) ^ k := by
    have h : 1 ≤ (x.length + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    calc c * (x.length + 1) ^ k + 1 ≤ c * (x.length + 1) ^ k + (x.length + 1) ^ k := by omega
      _ = (c + 1) * (x.length + 1) ^ k := by ring
  have h4 : (c * (x.length + 1) ^ k + 1) ^ 3 ≤ (c + 1) ^ 3 * (x.length + 1) ^ (3 * k) := by
    calc (c * (x.length + 1) ^ k + 1) ^ 3 ≤ ((c + 1) * (x.length + 1) ^ k) ^ 3 :=
          Nat.pow_le_pow_left h3 3
      _ = (c + 1) ^ 3 * (x.length + 1) ^ (3 * k) := by rw [mul_pow, ← pow_mul, mul_comm k 3]
  calc (reduction M c k x).length
      ≤ (M.numStates ^ 2 + 5 * M.transList.length + 22) *
          (c * (x.length + 1) ^ k + 1) ^ 3 := by rw [h1]; exact h2
    _ ≤ (M.numStates ^ 2 + 5 * M.transList.length + 22) *
          ((c + 1) ^ 3 * (x.length + 1) ^ (3 * k)) := Nat.mul_le_mul_left _ h4
    _ = (M.numStates ^ 2 + 5 * M.transList.length + 22) * (c + 1) ^ 3 *
          (x.length + 1) ^ (3 * k) := by ring

/-- **Cook–Levin: SAT is `NP`-hard.**

Every language `L` in `NP` (i.e. accepted by a nondeterministic Turing machine within a
polynomial number of steps) reduces to `SATLang` (the satisfiable CNF formulas): `x ∈ L`
if and only if the CNF formula `reduction M c k x` is satisfiable, and that formula has
polynomially many clauses in the length of `x`.

The reduction is not merely asserted to exist: it is the explicit, computable tableau
construction `Frontier.reduction`.  (An unrestricted existential `∃ f, ∀ x, x ∈ L ↔
Satisfiable (f x)` would be vacuous, since classically one could take `f x` to be `[]` or
`[[]]` according to whether `x ∈ L`.) -/
theorem cook_levin {L : Language} (hL : InNP L) :
    ∃ (M : NTM) (c k : ℕ),
      (∀ x, x ∈ L ↔ reduction M c k x ∈ SATLang) ∧
      ∃ a b : ℕ, ∀ x, (reduction M c k x).length ≤ a * (x.length + 1) ^ b := by
  obtain ⟨M, c, k, hM⟩ := hL
  refine ⟨M, c, k, fun x => ?_, ?_⟩
  · rw [hM x]
    exact (reduction_satisfiable_iff M c k x).symm
  · exact ⟨(M.numStates ^ 2 + 5 * M.transList.length + 22) * (c + 1) ^ 3, 3 * k,
      length_reduction_le M c k⟩

end Frontier

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

/-
Sanity checks: the notions defined here are not vacuous.  There are machines that accept
everything and machines that accept nothing, and correspondingly the tableau formula is
satisfiable in the first case and unsatisfiable in the second.
-/
import Mathlib
import RequestProject.CookLevin.Forward
import RequestProject.CookLevin.Backward

namespace Frontier

open Std.Sat

/-- The machine that immediately accepts every input. -/
def acceptAll : NTM where
  numStates := 1
  start := 0
  accept := 0
  start_lt := by norm_num
  accept_lt := by norm_num
  step _ a := [(0, a, Dir.stay)]
  step_lt := by
    intro q a r hr
    simp only [List.mem_singleton] at hr
    simp [hr]
  step_ne := by simp

theorem acceptAll_accepts (x : List Bool) (T : ℕ) : acceptAll.Accepts x T := by
  refine ⟨fun _ => acceptAll.init x, rfl, fun t _ => ?_, 0, Nat.zero_le T, rfl⟩
  exact ⟨Dir.stay, by simp [acceptAll, NTM.init], rfl, fun i _ => rfl⟩

theorem univ_mem_NP : InNP (Set.univ : Language) :=
  ⟨acceptAll, 0, 0, fun x => by simpa using acceptAll_accepts x 0⟩

/-- The machine that never accepts: it loops in its non-accepting start state. -/
def rejectAll : NTM where
  numStates := 2
  start := 0
  accept := 1
  start_lt := by norm_num
  accept_lt := by norm_num
  step _ a := [(0, a, Dir.stay)]
  step_lt := by
    intro q a r hr
    simp only [List.mem_singleton] at hr
    simp [hr]
  step_ne := by simp

theorem rejectAll_not_accepts (x : List Bool) (T : ℕ) : ¬ rejectAll.Accepts x T := by
  rintro ⟨r, hr0, hstep, t, htT, hacc⟩
  have key : ∀ s, s ≤ T → (r s).state = 0 := by
    intro s
    induction s with
    | zero => intro _; simp [hr0, NTM.init, rejectAll]
    | succ n ih =>
      intro hn
      obtain ⟨d, hmem, -, -⟩ := hstep n (by omega)
      simp only [rejectAll, List.mem_singleton, Prod.mk.injEq] at hmem
      exact hmem.1
  rw [key t htT] at hacc
  exact absurd hacc (by simp [rejectAll])

theorem empty_mem_NP : InNP (∅ : Language) :=
  ⟨rejectAll, 0, 0, fun x => by simpa using rejectAll_not_accepts x 0⟩

/-- The tableau of an accepting computation really is satisfiable. -/
theorem satisfiable_tableau_acceptAll (x : List Bool) (T : ℕ) :
    Satisfiable (tableau acceptAll x T) :=
  satisfiable_tableau_of_accepts (acceptAll_accepts x T)

/-- The tableau of a machine that never accepts really is unsatisfiable. -/
theorem not_satisfiable_tableau_rejectAll (x : List Bool) (T : ℕ) :
    ¬ Satisfiable (tableau rejectAll x T) := fun h =>
  rejectAll_not_accepts x T (accepts_of_satisfiable_tableau h)

end Frontier

/-
Short certificates for satisfiability: a satisfiable CNF formula is witnessed by a finite
list of bits, namely the values of the variables that actually occur in the formula.
-/
import Mathlib
import RequestProject.CookLevin.Sat

namespace Frontier

open Std.Sat

/-- An upper bound for the variables occurring in a CNF formula over `ℕ`. -/
def maxVar (f : CNF ℕ) : ℕ := (f.flatMap fun c => c.map Prod.fst).foldr max 0

theorem le_foldr_max {l : List ℕ} {v : ℕ} (h : v ∈ l) : v ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem le_maxVar {f : CNF ℕ} {v : ℕ} (h : CNF.Mem v f) : v ≤ maxVar f := by
  obtain ⟨c, hc, hv⟩ := h
  refine le_foldr_max ?_
  rw [List.mem_flatMap]
  refine ⟨c, hc, ?_⟩
  rcases hv with hv | hv <;> exact List.mem_map.2 ⟨_, hv, rfl⟩

/-- A CNF formula is satisfiable if and only if it has a certificate: a finite list of bits,
of length one more than the largest variable of the formula, that satisfies it. -/
theorem satisfiable_iff_exists_certificate (f : CNF ℕ) :
    Satisfiable f ↔ ∃ w : List Bool, w.length = maxVar f + 1 ∧
      CNF.eval (fun i => (w[i]?).getD false) f = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨(List.range (maxVar f + 1)).map σ, by simp, ?_⟩
    rw [CNF.eval_congr _ σ f ?_]
    · exact hσ
    · intro v hv
      have hlt : v < maxVar f + 1 := Nat.lt_succ_of_le (le_maxVar hv)
      simp [hlt]
  · rintro ⟨w, -, hw⟩
    exact ⟨_, hw⟩

end Frontier

/-
A single-tape nondeterministic Turing machine model with an explicit time bound,
and the resulting definition of the complexity class `NP`.
-/
import Mathlib

namespace Frontier

/-- Tape symbols: `none` is the blank symbol, `some b` is the bit `b`. -/
abbrev Sym := Option Bool

/-- The list of all tape symbols. -/
def allSyms : List Sym := [none, some false, some true]

@[simp] theorem mem_allSyms (a : Sym) : a ∈ allSyms := by
  cases a with
  | none => simp [allSyms]
  | some b => cases b <;> simp [allSyms]

/-- Head movement directions.  A left move at position `0` stays at `0`. -/
inductive Dir where
  | left : Dir
  | right : Dir
  | stay : Dir
deriving DecidableEq, Repr

instance : Inhabited Dir := ⟨Dir.stay⟩

/-- The list of all directions. -/
def allDirs : List Dir := [Dir.left, Dir.right, Dir.stay]

@[simp] theorem mem_allDirs (d : Dir) : d ∈ allDirs := by cases d <;> simp [allDirs]

/-- Effect of a direction on a head position (truncated subtraction at `0`). -/
def Dir.move : Dir → ℕ → ℕ
  | Dir.left, i => i - 1
  | Dir.right, i => i + 1
  | Dir.stay, i => i

theorem Dir.move_le (d : Dir) (i : ℕ) : d.move i ≤ i + 1 := by
  cases d <;> simp only [Dir.move] <;> omega

/-- A single-tape nondeterministic Turing machine over the alphabet `Sym`.
States are natural numbers below `numStates`.  The transition function returns the
(finite) list of possible successor triples `(newState, newSymbol, direction)`. -/
structure NTM where
  numStates : ℕ
  start : ℕ
  accept : ℕ
  start_lt : start < numStates
  accept_lt : accept < numStates
  step : ℕ → Sym → List (ℕ × Sym × Dir)
  step_lt : ∀ q a, ∀ r ∈ step q a, r.1 < numStates
  /-- The machine is total: it never gets stuck. -/
  step_ne : ∀ q a, q < numStates → step q a ≠ []

/-- A configuration: current state, tape contents, head position. -/
structure Cfg where
  state : ℕ
  tape : ℕ → Sym
  head : ℕ

namespace NTM

variable (M : NTM)

/-- The initial configuration on input `x`. -/
def init (x : List Bool) : Cfg := ⟨M.start, fun i => x[i]?, 0⟩

/-- The one-step relation of `M`. -/
def Next (c c' : Cfg) : Prop :=
  ∃ d : Dir, (c'.state, c'.tape c.head, d) ∈ M.step c.state (c.tape c.head) ∧
    c'.head = d.move c.head ∧ ∀ i, i ≠ c.head → c'.tape i = c.tape i

/-- `M` accepts `x` within `T` steps: there is a length-`T` computation starting from the
initial configuration on `x` that visits the accepting state at some time `t ≤ T`. -/
def Accepts (x : List Bool) (T : ℕ) : Prop :=
  ∃ r : ℕ → Cfg, r 0 = M.init x ∧ (∀ t, t < T → M.Next (r t) (r (t + 1))) ∧
    ∃ t, t ≤ T ∧ (r t).state = M.accept

theorem head_le_of_run {r : ℕ → Cfg} {T : ℕ} (hr0 : r 0 = M.init x)
    (hstep : ∀ t, t < T → M.Next (r t) (r (t + 1))) : ∀ t, t ≤ T → (r t).head ≤ t := by
  intro t
  induction t with
  | zero => intro _; simp [hr0, init]
  | succ n ih =>
    intro hn
    obtain ⟨d, _, hh, _⟩ := hstep n (by omega)
    have := ih (by omega)
    have := Dir.move_le d (r n).head
    omega

theorem state_lt_of_run {r : ℕ → Cfg} {T : ℕ} (hr0 : r 0 = M.init x)
    (hstep : ∀ t, t < T → M.Next (r t) (r (t + 1))) :
    ∀ t, t ≤ T → (r t).state < M.numStates := by
  intro t
  induction t with
  | zero => intro _; simp [hr0, init]; exact M.start_lt
  | succ n ih =>
    intro hn
    obtain ⟨d, hmem, _, _⟩ := hstep n (by omega)
    exact M.step_lt _ _ _ hmem

/-- An arbitrary successor configuration (used to extend a computation that has already
accepted; the machine is total, so this is always a genuine successor). -/
def someNext (c : Cfg) : Cfg :=
  let r := (M.step c.state (c.tape c.head)).headI
  ⟨r.1, Function.update c.tape c.head r.2.1, r.2.2.move c.head⟩

theorem next_someNext {c : Cfg} (hc : c.state < M.numStates) : M.Next c (M.someNext c) := by
  have hne : M.step c.state (c.tape c.head) ≠ [] := M.step_ne _ _ hc
  obtain ⟨r, rest, hl⟩ : ∃ r rest, M.step c.state (c.tape c.head) = r :: rest := by
    cases h : M.step c.state (c.tape c.head) with
    | nil => exact absurd h hne
    | cons a l => exact ⟨a, l, rfl⟩
  have hs : M.someNext c =
      ⟨r.1, Function.update c.tape c.head r.2.1, r.2.2.move c.head⟩ := by
    simp [someNext, hl]
  rw [hs]
  refine ⟨r.2.2, ?_, rfl, fun i hi => Function.update_of_ne hi _ _⟩
  simp only [Function.update_self]
  rw [hl]
  simp

theorem someNext_state_lt {c : Cfg} (hc : c.state < M.numStates) :
    (M.someNext c).state < M.numStates := by
  obtain ⟨d, hmem, -, -⟩ := M.next_someNext hc
  exact M.step_lt c.state (c.tape c.head)
    ((M.someNext c).state, (M.someNext c).tape c.head, d) hmem

/-- `Accepts` is the usual notion: some computation of length at most `T` reaches the
accepting state.  (A shorter accepting computation can always be extended, because the
machine is total.) -/
theorem accepts_iff (x : List Bool) (T : ℕ) :
    M.Accepts x T ↔ ∃ t, t ≤ T ∧ ∃ r : ℕ → Cfg, r 0 = M.init x ∧
      (∀ s, s < t → M.Next (r s) (r (s + 1))) ∧ (r t).state = M.accept := by
  constructor
  · rintro ⟨r, hr0, hstep, t, htT, hacc⟩
    exact ⟨t, htT, r, hr0, fun s hs => hstep s (lt_of_lt_of_le hs htT), hacc⟩
  · rintro ⟨t, htT, r, hr0, hstep, hacc⟩
    have hstate : (r t).state < M.numStates := M.state_lt_of_run hr0 hstep t le_rfl
    have hiter : ∀ n, (M.someNext^[n] (r t)).state < M.numStates := by
      intro n
      induction n with
      | zero => simpa using hstate
      | succ m ih => rw [Function.iterate_succ_apply']; exact M.someNext_state_lt ih
    refine ⟨fun s => if s ≤ t then r s else M.someNext^[s - t] (r t), by simp [hr0], ?_,
      t, htT, by simp [hacc]⟩
    intro s _
    by_cases hs : s + 1 ≤ t
    · simp only [if_pos hs, if_pos (by omega : s ≤ t)]
      exact hstep s (by omega)
    · by_cases hs' : s ≤ t
      · have hst : s = t := by omega
        subst hst
        simp only [if_pos le_rfl, if_neg hs]
        have : s + 1 - s = 1 := by omega
        rw [this]
        simpa using M.next_someNext hstate
      · simp only [if_neg hs, if_neg hs']
        have h1 : s + 1 - t = (s - t) + 1 := by omega
        rw [h1, Function.iterate_succ_apply']
        exact M.next_someNext (hiter _)

end NTM

/-- A language is a set of bit strings. -/
abbrev Language := Set (List Bool)

/-- `L ∈ NP`: some nondeterministic Turing machine accepts exactly `L`, within a
polynomial number of steps. -/
def InNP (L : Language) : Prop :=
  ∃ (M : NTM) (c k : ℕ), ∀ x, x ∈ L ↔ M.Accepts x (c * (x.length + 1) ^ k)

end Frontier

/-
The tableau formula has polynomially many clauses.
-/
import Mathlib
import RequestProject.CookLevin.Tableau

namespace Frontier

open Std.Sat

theorem length_flatMap_le {α β : Type*} (l : List α) (g : α → List β) (b : ℕ)
    (h : ∀ a ∈ l, (g a).length ≤ b) : (l.flatMap g).length ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih fun c hc => h c (by simp [hc])
    calc (g a).length + (l.flatMap g).length ≤ b + l.length * b := by omega
      _ = (l.length + 1) * b := by ring

theorem length_atMostOne_le {α : Type*} [DecidableEq α] (vs : List α) :
    (atMostOne vs).length ≤ vs.length * vs.length := by
  refine length_flatMap_le _ _ _ fun v _ => ?_
  refine le_trans (length_flatMap_le _ _ 1 fun w _ => ?_) (by simp)
  by_cases h : v = w <;> simp [h]

theorem length_exactlyOne_le {α : Type*} [DecidableEq α] (vs : List α) :
    (exactlyOne vs).length ≤ 1 + vs.length * vs.length := by
  simp only [exactlyOne, List.length_cons]
  have := length_atMostOne_le vs
  omega

variable (M : NTM) (x : List Bool) (T : ℕ)

private theorem cube1 : T + 1 ≤ (T + 1) ^ 3 := Nat.le_self_pow (by norm_num) _

private theorem cube2 : (T + 1) * (T + 1) ≤ (T + 1) ^ 3 := by
  have : (T + 1) ^ 2 ≤ (T + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  nlinarith [this]

theorem length_stateClauses_le :
    (stateClauses M T).length ≤ (1 + M.numStates ^ 2) * (T + 1) ^ 3 := by
  have h1 : (stateClauses M T).length ≤ (T + 1) * (1 + M.numStates * M.numStates) := by
    have := length_flatMap_le (List.range (T + 1))
      (fun t => exactlyOne ((List.range M.numStates).map (TVar.st t)))
      (1 + M.numStates * M.numStates)
      (fun t _ => by simpa using length_exactlyOne_le ((List.range M.numStates).map (TVar.st t)))
    simpa [stateClauses] using this
  have h2 : T + 1 ≤ (T + 1) ^ 3 := cube1 T
  calc (stateClauses M T).length ≤ (T + 1) * (1 + M.numStates * M.numStates) := h1
    _ ≤ (1 + M.numStates ^ 2) * (T + 1) ^ 3 := by nlinarith [h2]

theorem length_headClauses_le : (headClauses T).length ≤ 2 * (T + 1) ^ 3 := by
  have h1 : (headClauses T).length ≤ (T + 1) * (1 + (T + 1) * (T + 1)) := by
    have := length_flatMap_le (List.range (T + 1))
      (fun t => exactlyOne ((List.range (T + 1)).map (TVar.hd t))) (1 + (T + 1) * (T + 1))
      (fun t _ => by simpa using length_exactlyOne_le ((List.range (T + 1)).map (TVar.hd t)))
    simpa [headClauses] using this
  have h2 : T + 1 ≤ (T + 1) ^ 3 := cube1 T
  calc (headClauses T).length ≤ (T + 1) * (1 + (T + 1) * (T + 1)) := h1
    _ ≤ 2 * (T + 1) ^ 3 := by nlinarith [h2]

theorem length_cellClauses_le : (cellClauses T).length ≤ 10 * (T + 1) ^ 3 := by
  have h1 : (cellClauses T).length ≤ (T + 1) * ((T + 1) * 10) := by
    have := length_flatMap_le (List.range (T + 1))
      (fun t => (List.range (T + 1)).flatMap fun i => exactlyOne (allSyms.map (TVar.cell t i)))
      ((T + 1) * 10) (fun t _ => by
        have := length_flatMap_le (List.range (T + 1))
          (fun i => exactlyOne (allSyms.map (TVar.cell t i))) 10
          (fun i _ => by simpa [allSyms] using length_exactlyOne_le (allSyms.map (TVar.cell t i)))
        simpa using this)
    simpa [cellClauses] using this
  have h2 : (T + 1) * (T + 1) ≤ (T + 1) ^ 3 := cube2 T
  calc (cellClauses T).length ≤ (T + 1) * ((T + 1) * 10) := h1
    _ ≤ 10 * (T + 1) ^ 3 := by nlinarith [h2]

theorem length_initClauses_le : (initClauses M x T).length ≤ 3 * (T + 1) ^ 3 := by
  have h2 : T + 1 ≤ (T + 1) ^ 3 := cube1 T
  have h : (initClauses M x T).length ≤ T + 3 := by simp [initClauses]
  omega

theorem length_acceptClauses_le : (acceptClauses M T).length ≤ (T + 1) ^ 3 := by
  have h2 : T + 1 ≤ (T + 1) ^ 3 := cube1 T
  simp only [acceptClauses, List.length_singleton]
  omega

theorem length_headBoundClauses_le : (headBoundClauses T).length ≤ (T + 1) ^ 3 := by
  have h2 : T + 1 ≤ (T + 1) ^ 3 := cube1 T
  simp only [headBoundClauses, List.length_map, List.length_range]
  omega

theorem length_transClauses_le :
    (transClauses M T).length ≤ (1 + 5 * M.transList.length) * (T + 1) ^ 3 := by
  have hlen : (transClauses M T).length ≤ T + T * (M.transList.length * (2 + (T + 1) * 3)) := by
    simp only [transClauses, List.length_append]
    refine Nat.add_le_add (by simp) ?_
    refine le_trans (length_flatMap_le _ _ (M.transList.length * (2 + (T + 1) * 3)) ?_) (by simp)
    intro t _
    refine le_trans (length_flatMap_le _ _ (2 + (T + 1) * 3) ?_) (by simp)
    intro j _
    simp only [List.length_append, List.length_cons, List.length_nil]
    have hi : ((List.range (T + 1)).flatMap fun i =>
        [ implClause [TVar.mv t j, TVar.hd t i] (TVar.cell t i (M.trAt j).a),
          implClause [TVar.mv t j, TVar.hd t i] (TVar.cell (t + 1) i (M.trAt j).a'),
          implClause [TVar.mv t j, TVar.hd t i]
            (TVar.hd (t + 1) ((M.trAt j).d.move i)) ]).length ≤ (T + 1) * 3 :=
      le_trans (length_flatMap_le _ _ 3 (fun i _ => Nat.le_refl 3)) (by simp)
    omega
  have h2 : T + 1 ≤ (T + 1) ^ 3 := cube1 T
  have h3 : (T + 1) * (T + 1) ≤ (T + 1) ^ 3 := cube2 T
  have key : T * (M.transList.length * (2 + (T + 1) * 3)) ≤
      5 * M.transList.length * (T + 1) ^ 3 := by
    have e1 : T * (M.transList.length * (2 + (T + 1) * 3)) ≤
        (T + 1) * (M.transList.length * (5 * (T + 1))) := by
      have h5 : 2 + (T + 1) * 3 ≤ 5 * (T + 1) := by omega
      exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ h5)
    calc T * (M.transList.length * (2 + (T + 1) * 3))
        ≤ (T + 1) * (M.transList.length * (5 * (T + 1))) := e1
      _ = 5 * M.transList.length * ((T + 1) * (T + 1)) := by ring
      _ ≤ 5 * M.transList.length * (T + 1) ^ 3 := Nat.mul_le_mul_left _ h3
  have expand : (1 + 5 * M.transList.length) * (T + 1) ^ 3 =
      (T + 1) ^ 3 + 5 * M.transList.length * (T + 1) ^ 3 := by ring
  omega

theorem length_inertiaClauses_le : (inertiaClauses T).length ≤ 3 * (T + 1) ^ 3 := by
  have h1 : (inertiaClauses T).length ≤ T * ((T + 1) * ((T + 1) * 3)) := by
    simp only [inertiaClauses]
    refine le_trans (length_flatMap_le _ _ ((T + 1) * ((T + 1) * 3)) ?_) (by simp)
    intro t _
    refine le_trans (length_flatMap_le _ _ ((T + 1) * 3) ?_) (by simp)
    intro i _
    refine le_trans (length_flatMap_le _ _ 3 ?_) (by simp)
    intro k _
    by_cases hk : k = i <;> simp [hk, allSyms]
  have h3 : (T + 1) * (T + 1) ≤ (T + 1) ^ 3 := cube2 T
  calc (inertiaClauses T).length ≤ T * ((T + 1) * ((T + 1) * 3)) := h1
    _ ≤ 3 * (T + 1) ^ 3 := by nlinarith [h3]

/-- The number of clauses of the tableau is cubic in the time bound. -/
theorem length_tableau_le :
    (tableau M x T).length ≤
      (M.numStates ^ 2 + 5 * M.transList.length + 22) * (T + 1) ^ 3 := by
  have e : (tableau M x T).length =
      (stateClauses M T).length + (headClauses T).length + (cellClauses T).length +
      (initClauses M x T).length + (acceptClauses M T).length +
      (headBoundClauses T).length + (transClauses M T).length +
      (inertiaClauses T).length := by
    simp only [tableau, List.length_append]
  have h1 := length_stateClauses_le M T
  have h2 := length_headClauses_le T
  have h3 := length_cellClauses_le T
  have h4 := length_initClauses_le M x T
  have h5 := length_acceptClauses_le M T
  have h6 := length_headBoundClauses_le T
  have h7 := length_transClauses_le M T
  have h8 := length_inertiaClauses_le T
  have expand : (M.numStates ^ 2 + 5 * M.transList.length + 22) * (T + 1) ^ 3 =
      (1 + M.numStates ^ 2) * (T + 1) ^ 3 + 2 * (T + 1) ^ 3 + 10 * (T + 1) ^ 3 +
      3 * (T + 1) ^ 3 + (T + 1) ^ 3 + (T + 1) ^ 3 +
      (1 + 5 * M.transList.length) * (T + 1) ^ 3 + 3 * (T + 1) ^ 3 := by ring
  omega

end Frontier

/-
From a satisfying assignment of the tableau back to an accepting computation.
-/
import Mathlib
import RequestProject.CookLevin.Tableau

namespace Frontier

open Std.Sat

variable {M : NTM} {x : List Bool} {T : ℕ} {σ : TVar → Bool}

open Classical in
/-- The state described by the assignment `σ` at time `t`. -/
noncomputable def stateAt (M : NTM) (σ : TVar → Bool) (t : ℕ) : ℕ :=
  if h : ∃ q, q < M.numStates ∧ σ (TVar.st t q) = true then h.choose else 0

open Classical in
/-- The head position described by the assignment `σ` at time `t`. -/
noncomputable def headAt (T : ℕ) (σ : TVar → Bool) (t : ℕ) : ℕ :=
  if h : ∃ i, i ≤ T ∧ σ (TVar.hd t i) = true then h.choose else 0

/-- The symbol described by the assignment `σ` in cell `i` at time `t`. -/
def cellAt (σ : TVar → Bool) (t i : ℕ) : Sym :=
  if σ (TVar.cell t i (some true)) = true then some true
  else if σ (TVar.cell t i (some false)) = true then some false else none

theorem stateAt_spec {t : ℕ} (h : ∃ q, q < M.numStates ∧ σ (TVar.st t q) = true) :
    stateAt M σ t < M.numStates ∧ σ (TVar.st t (stateAt M σ t)) = true := by
  rw [stateAt, dif_pos h]
  exact h.choose_spec

theorem headAt_spec {t : ℕ} (h : ∃ i, i ≤ T ∧ σ (TVar.hd t i) = true) :
    headAt T σ t ≤ T ∧ σ (TVar.hd t (headAt T σ t)) = true := by
  rw [headAt, dif_pos h]
  exact h.choose_spec

theorem cellAt_spec {t i : ℕ} (hex : ∃ a : Sym, σ (TVar.cell t i a) = true) :
    σ (TVar.cell t i (cellAt σ t i)) = true := by
  obtain ⟨a, ha⟩ := hex
  rw [cellAt]
  by_cases h1 : σ (TVar.cell t i (some true)) = true
  · simp [h1]
  · by_cases h2 : σ (TVar.cell t i (some false)) = true
    · simp [h1, h2]
    · have hnone : a = none := by
        rcases a with _ | b
        · rfl
        · cases b
          · exact absurd ha h2
          · exact absurd ha h1
      rw [hnone] at ha
      simpa [h1, h2] using ha

theorem accepts_of_satisfiable_tableau (h : Satisfiable (tableau M x T)) : M.Accepts x T := by
  obtain ⟨σ, hσ⟩ := h
  rw [eval_tableau_iff, eval_stateClauses_iff, eval_headClauses_iff, eval_cellClauses_iff,
    eval_initClauses_iff, eval_acceptClauses_iff, eval_headBoundClauses_iff,
    eval_transClauses_iff, eval_inertiaClauses_iff] at hσ
  obtain ⟨hst, hhd, hce, ⟨hin1, hin2, hin3⟩, hacc, hhb, ⟨htr1, htr2⟩, hinert⟩ := hσ
  -- the state, head and cell functions determined by `σ`
  have hSspec : ∀ t ≤ T, stateAt M σ t < M.numStates ∧ σ (TVar.st t (stateAt M σ t)) = true :=
    fun t ht => stateAt_spec (hst t ht).1
  have hSuniq : ∀ t ≤ T, ∀ q < M.numStates, σ (TVar.st t q) = true → q = stateAt M σ t :=
    fun t ht q hq hq' => (hst t ht).2 q hq _ (hSspec t ht).1 hq' (hSspec t ht).2
  have hHspec : ∀ t ≤ T, headAt T σ t ≤ T ∧ σ (TVar.hd t (headAt T σ t)) = true :=
    fun t ht => headAt_spec (hhd t ht).1
  have hHuniq : ∀ t ≤ T, ∀ i ≤ T, σ (TVar.hd t i) = true → i = headAt T σ t :=
    fun t ht i hi hi' => (hhd t ht).2 i hi _ (hHspec t ht).1 hi' (hHspec t ht).2
  have hCspec : ∀ t ≤ T, ∀ i ≤ T, σ (TVar.cell t i (cellAt σ t i)) = true :=
    fun t ht i hi => cellAt_spec (hce t ht i hi).1
  have hCuniq : ∀ t ≤ T, ∀ i ≤ T, ∀ a : Sym, σ (TVar.cell t i a) = true → a = cellAt σ t i :=
    fun t ht i hi a ha => (hce t ht i hi).2 a _ ha (hCspec t ht i hi)
  refine ⟨fun t => ⟨stateAt M σ (min t T),
      fun i => if i ≤ T then cellAt σ (min t T) i else x[i]?, headAt T σ (min t T)⟩, ?_, ?_, ?_⟩
  · -- the initial configuration
    have h0 : min 0 T = 0 := Nat.zero_min T
    simp only [h0, NTM.init, Cfg.mk.injEq]
    refine ⟨(hSuniq 0 (Nat.zero_le T) M.start M.start_lt hin1).symm, ?_,
      (hHuniq 0 (Nat.zero_le T) 0 (Nat.zero_le T) hin2).symm⟩
    funext i
    by_cases hi : i ≤ T
    · simp only [hi, if_pos]
      exact (hCuniq 0 (Nat.zero_le T) i hi _ (hin3 i hi)).symm
    · simp [hi]
  · -- the transition steps
    intro t ht
    have htT : min t T = t := min_eq_left (le_of_lt ht)
    have ht1T : min (t + 1) T = t + 1 := min_eq_left ht
    obtain ⟨j, hj, hmv⟩ := htr1 t ht
    obtain ⟨hq, hq', hrest⟩ := htr2 t ht j hj hmv
    have htrmem : M.trAt j ∈ M.transList := M.trAt_mem hj
    rw [NTM.mem_transList] at htrmem
    obtain ⟨hqlt, hstepmem⟩ := htrmem
    have hq'lt : (M.trAt j).q' < M.numStates := M.step_lt _ _ _ hstepmem
    -- the head position at time `t`
    set i := headAt T σ t with hi
    have hiT : i ≤ T := (hHspec t (le_of_lt ht)).1
    have hiσ : σ (TVar.hd t i) = true := (hHspec t (le_of_lt ht)).2
    have hiltT : i < T := by
      rcases lt_or_eq_of_le hiT with h | h
      · exact h
      · rw [h] at hiσ
        rw [hhb t ht] at hiσ
        exact absurd hiσ (by simp)
    obtain ⟨hca, hca', hcd⟩ := hrest i hiT hiσ
    have hSq : (M.trAt j).q = stateAt M σ t := hSuniq t (le_of_lt ht) _ hqlt hq
    have hSq' : (M.trAt j).q' = stateAt M σ (t + 1) := hSuniq (t + 1) ht _ hq'lt hq'
    have hCa : (M.trAt j).a = cellAt σ t i := hCuniq t (le_of_lt ht) i hiT _ hca
    have hCa' : (M.trAt j).a' = cellAt σ (t + 1) i := hCuniq (t + 1) ht i hiT _ hca'
    have hmoveT : (M.trAt j).d.move i ≤ T := le_trans ((M.trAt j).d.move_le i) hiltT
    have hHd' : (M.trAt j).d.move i = headAt T σ (t + 1) :=
      hHuniq (t + 1) ht _ hmoveT hcd
    refine ⟨(M.trAt j).d, ?_, ?_, ?_⟩
    · simp only [htT, ht1T, hiT, if_pos, ← hi]
      rw [← hSq, ← hSq', ← hCa, ← hCa']
      · exact hstepmem
    · simp only [htT, ht1T, ← hi]
      rw [← hHd']
    · intro k hk
      simp only [htT, ht1T, ← hi] at hk ⊢
      by_cases hkT : k ≤ T
      · simp only [hkT, if_pos]
        exact (hCuniq (t + 1) ht k hkT _
          (hinert t ht i hiT k hkT hk _ hiσ (hCspec t (le_of_lt ht) k hkT))).symm
      · simp [hkT]
  · -- the accepting time
    obtain ⟨t, htT, hσt⟩ := hacc
    refine ⟨t, htT, ?_⟩
    simp only [min_eq_left htT]
    exact (hSuniq t htT M.accept M.accept_lt hσt).symm

end Frontier

/-
Basic SAT vocabulary, built on the `Std.Sat.CNF` datatype from the Lean core library.
-/
import Mathlib
import Std.Sat.CNF.Relabel

namespace Frontier

open Std.Sat

/-- A CNF formula is satisfiable if some assignment evaluates it to `true`. -/
def Satisfiable {α : Type*} (f : CNF α) : Prop := ∃ σ : α → Bool, CNF.eval σ f = true

theorem satisfiable_iff_not_unsat {α : Type*} (f : CNF α) :
    Satisfiable f ↔ ¬ CNF.Unsat f := by
  constructor
  · rintro ⟨σ, hσ⟩ h
    have := h σ
    simp [hσ] at this
  · intro h
    by_contra hc
    refine h fun σ => ?_
    simpa using (fun hh => hc ⟨σ, hh⟩ : ¬ (CNF.eval σ f = true))

/-- Satisfiability is invariant under injective renaming of the variables. -/
theorem satisfiable_relabel_iff {α β : Type*} {f : CNF α} {r : α → β}
    (hr : Function.Injective r) : Satisfiable (CNF.relabel r f) ↔ Satisfiable f := by
  rw [satisfiable_iff_not_unsat, satisfiable_iff_not_unsat, not_iff_not]
  exact CNF.unsat_relabel_iff (fun _ _ h => hr h)

/-- The SAT language: satisfiable CNF formulas with natural-number variables. -/
def SATLang : Set (CNF ℕ) := {f | Satisfiable f}

end Frontier

/-
From an accepting computation to a satisfying assignment of the tableau.
-/
import Mathlib
import RequestProject.CookLevin.Tableau

namespace Frontier

open Std.Sat

/-- `j` is (the index of) a transition witnessing the step from `c` to `c'`. -/
def stepProp (M : NTM) (c c' : Cfg) (j : ℕ) : Prop :=
  j < M.transList.length ∧ (M.trAt j).q = c.state ∧ (M.trAt j).a = c.tape c.head ∧
    (M.trAt j).q' = c'.state ∧ (M.trAt j).a' = c'.tape c.head ∧
    c'.head = (M.trAt j).d.move c.head

theorem exists_stepProp {M : NTM} {c c' : Cfg} (hq : c.state < M.numStates)
    (h : M.Next c c') : ∃ j, stepProp M c c' j := by
  obtain ⟨d, hmem, hhead, -⟩ := h
  have htr : (⟨c.state, c.tape c.head, c'.state, c'.tape c.head, d⟩ : Trans) ∈ M.transList := by
    rw [NTM.mem_transList]
    exact ⟨hq, hmem⟩
  obtain ⟨j, hj, hget⟩ := M.exists_trAt htr
  exact ⟨j, hj, by rw [hget], by rw [hget], by rw [hget], by rw [hget], by rw [hget]; exact hhead⟩

open Classical in
/-- A choice of transition index for each step of the computation `r`. -/
noncomputable def chosen (M : NTM) (r : ℕ → Cfg) (t : ℕ) : ℕ :=
  if h : ∃ j, stepProp M (r t) (r (t + 1)) j then h.choose else 0

theorem chosen_spec {M : NTM} {r : ℕ → Cfg} {t : ℕ}
    (h : ∃ j, stepProp M (r t) (r (t + 1)) j) : stepProp M (r t) (r (t + 1)) (chosen M r t) := by
  rw [chosen, dif_pos h]
  exact h.choose_spec


/-- The assignment read off from a computation. -/
noncomputable def runAssign (M : NTM) (r : ℕ → Cfg) : TVar → Bool
  | TVar.st t q => decide ((r t).state = q)
  | TVar.hd t i => decide ((r t).head = i)
  | TVar.cell t i a => decide ((r t).tape i = a)
  | TVar.mv t j => decide (j = chosen M r t)

variable {M : NTM} {x : List Bool} {T : ℕ}

theorem satisfiable_tableau_of_accepts (h : M.Accepts x T) : Satisfiable (tableau M x T) := by
  obtain ⟨r, hr0, hstep, tacc, htacc, haccept⟩ := h
  have hhead : ∀ t, t ≤ T → (r t).head ≤ t := M.head_le_of_run hr0 hstep
  have hstate : ∀ t, t ≤ T → (r t).state < M.numStates := M.state_lt_of_run hr0 hstep
  have hchosen : ∀ t, t < T → stepProp M (r t) (r (t + 1)) (chosen M r t) := by
    intro t ht
    exact chosen_spec (exists_stepProp (hstate t (by omega)) (hstep t ht))
  refine ⟨runAssign M r, ?_⟩
  rw [eval_tableau_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eval_stateClauses_iff]
    intro t ht
    refine ⟨⟨(r t).state, hstate t ht, by simp [runAssign]⟩, ?_⟩
    intro q _ q' _ hq hq'
    simp only [runAssign, decide_eq_true_eq] at hq hq'
    omega
  · rw [eval_headClauses_iff]
    intro t ht
    refine ⟨⟨(r t).head, le_trans (hhead t ht) ht, by simp [runAssign]⟩, ?_⟩
    intro i _ i' _ hi hi'
    simp only [runAssign, decide_eq_true_eq] at hi hi'
    omega
  · rw [eval_cellClauses_iff]
    intro t ht i hi
    refine ⟨⟨(r t).tape i, by simp [runAssign]⟩, ?_⟩
    intro a b ha hb
    simp only [runAssign, decide_eq_true_eq] at ha hb
    rw [← ha, ← hb]
  · rw [eval_initClauses_iff]
    refine ⟨by simp [runAssign, hr0, NTM.init], by simp [runAssign, hr0, NTM.init], ?_⟩
    intro i _
    simp [runAssign, hr0, NTM.init]
  · rw [eval_acceptClauses_iff]
    exact ⟨tacc, htacc, by simp [runAssign, haccept]⟩
  · rw [eval_headBoundClauses_iff]
    intro t ht
    have := hhead t (by omega)
    simp only [runAssign, decide_eq_false_iff_not]
    omega
  · rw [eval_transClauses_iff]
    constructor
    · intro t ht
      exact ⟨chosen M r t, (hchosen t ht).1, by simp [runAssign]⟩
    · intro t ht j _ hmv
      simp only [runAssign, decide_eq_true_eq] at hmv
      subst hmv
      obtain ⟨-, hq, ha, hq', ha', hd⟩ := hchosen t ht
      refine ⟨by simp [runAssign, hq], by simp [runAssign, hq'], ?_⟩
      intro i _ hi
      simp only [runAssign, decide_eq_true_eq] at hi
      subst hi
      exact ⟨by simp [runAssign, ha], by simp [runAssign, ha'], by simp [runAssign, hd]⟩
  · rw [eval_inertiaClauses_iff]
    intro t ht i _ k _ hne a hhd hcell
    simp only [runAssign, decide_eq_true_eq] at hhd hcell ⊢
    obtain ⟨d, -, -, hsame⟩ := hstep t ht
    rw [hsame k (by omega), hcell]

end Frontier

/-
The Cook–Levin tableau: a CNF formula describing an accepting computation of a
nondeterministic Turing machine.
-/
import Mathlib
import RequestProject.CookLevin.Sat
import RequestProject.CookLevin.Machine

namespace Frontier

open Std.Sat

/-! ### Generic CNF toolkit -/

theorem eval_iff {α : Type*} (σ : α → Bool) (f : CNF α) :
    CNF.eval σ f = true ↔ ∀ c ∈ f, CNF.Clause.eval σ c = true := List.all_eq_true

theorem eval_flatMap {α β : Type*} (σ : α → Bool) (l : List β) (g : β → CNF α) :
    CNF.eval σ (l.flatMap g) = true ↔ ∀ b ∈ l, CNF.eval σ (g b) = true := by
  simp [eval_iff, List.mem_flatMap]
  tauto

theorem eval_map_singleton {α β : Type*} (σ : α → Bool) (l : List β)
    (g : β → CNF.Clause α) :
    CNF.eval σ (l.map fun b => g b) = true ↔ ∀ b ∈ l, CNF.Clause.eval σ (g b) = true := by
  simp [eval_iff]

/-- A clause asserting that at least one of the variables `vs` is true. -/
def atLeastOne {α : Type*} (vs : List α) : CNF.Clause α := vs.map fun v => (v, true)

/-- Clauses asserting that at most one of the variables `vs` is true. -/
def atMostOne {α : Type*} [DecidableEq α] (vs : List α) : CNF α :=
  vs.flatMap fun v => vs.flatMap fun w => if v = w then [] else [[(v, false), (w, false)]]

/-- Clauses asserting that exactly one of the variables `vs` is true. -/
def exactlyOne {α : Type*} [DecidableEq α] (vs : List α) : CNF α :=
  atLeastOne vs :: atMostOne vs

/-- A clause encoding the implication `(⋀ hyps) → concl`. -/
def implClause {α : Type*} (hyps : List α) (concl : α) : CNF.Clause α :=
  (hyps.map fun v => (v, false)) ++ [(concl, true)]

theorem eval_atLeastOne {α : Type*} (σ : α → Bool) (vs : List α) :
    CNF.Clause.eval σ (atLeastOne vs) = true ↔ ∃ v ∈ vs, σ v = true := by
  simp [CNF.Clause.eval, atLeastOne]

theorem eval_atLeastOne_map {α β : Type*} (σ : α → Bool) (l : List β) (g : β → α) :
    CNF.Clause.eval σ (atLeastOne (l.map g)) = true ↔ ∃ b ∈ l, σ (g b) = true := by
  simp [CNF.Clause.eval, atLeastOne]

theorem eval_atMostOne {α : Type*} [DecidableEq α] (σ : α → Bool) (vs : List α) :
    CNF.eval σ (atMostOne vs) = true ↔
      ∀ v ∈ vs, ∀ w ∈ vs, σ v = true → σ w = true → v = w := by
  simp only [atMostOne, eval_flatMap]
  constructor
  · intro h v hv w hw hv' hw'
    by_contra hne
    have := h v hv w hw
    rw [if_neg hne] at this
    simp [CNF.Clause.eval, hv', hw'] at this
  · intro h v hv w hw
    by_cases hvw : v = w
    · simp [hvw]
    · rw [if_neg hvw]
      simp only [eval_iff, List.mem_singleton]
      rintro c rfl
      simp only [CNF.Clause.eval, List.any_cons, List.any_nil, beq_iff_eq, Bool.or_false,
        Bool.or_eq_true]
      by_cases hv' : σ v = true
      · by_cases hw' : σ w = true
        · exact absurd (h v hv w hw hv' hw') hvw
        · exact Or.inr (Bool.eq_false_iff.2 hw')
      · exact Or.inl (Bool.eq_false_iff.2 hv')

theorem eval_exactlyOne {α : Type*} [DecidableEq α] (σ : α → Bool) (vs : List α) :
    CNF.eval σ (exactlyOne vs) = true ↔
      (∃ v ∈ vs, σ v = true) ∧ ∀ v ∈ vs, ∀ w ∈ vs, σ v = true → σ w = true → v = w := by
  rw [exactlyOne, CNF.eval_cons]
  simp only [Bool.and_eq_true, eval_atLeastOne, eval_atMostOne]

theorem eval_implClause {α : Type*} (σ : α → Bool) (hyps : List α) (concl : α) :
    CNF.Clause.eval σ (implClause hyps concl) = true ↔
      ((∀ v ∈ hyps, σ v = true) → σ concl = true) := by
  simp only [implClause, CNF.Clause.eval, List.any_append, List.any_map, List.any_cons,
    List.any_nil, Bool.or_false, Bool.or_eq_true, List.any_eq_true, Function.comp_apply,
    beq_iff_eq]
  constructor
  · rintro (⟨v, hv, hv'⟩ | h) hall
    · exact absurd (hall v hv) (by simp [hv'])
    · exact h
  · intro h
    by_cases hall : ∀ v ∈ hyps, σ v = true
    · exact Or.inr (h hall)
    · push_neg at hall
      obtain ⟨v, hv, hv'⟩ := hall
      exact Or.inl ⟨v, hv, Bool.eq_false_iff.2 hv'⟩

theorem eval_posUnit {α : Type*} (σ : α → Bool) (v : α) :
    CNF.Clause.eval σ [(v, true)] = true ↔ σ v = true := by simp [CNF.Clause.eval]

theorem eval_negUnit {α : Type*} (σ : α → Bool) (v : α) :
    CNF.Clause.eval σ [(v, false)] = true ↔ σ v = false := by simp [CNF.Clause.eval]

/-! ### Tableau variables -/

/-- Variables of the tableau formula. -/
inductive TVar where
  /-- At time `t` the machine is in state `q`. -/
  | st : ℕ → ℕ → TVar
  /-- At time `t` the head is at position `i`. -/
  | hd : ℕ → ℕ → TVar
  /-- At time `t` the tape cell `i` contains symbol `a`. -/
  | cell : ℕ → ℕ → Sym → TVar
  /-- At time `t` the machine uses transition number `j`. -/
  | mv : ℕ → ℕ → TVar
deriving DecidableEq

/-- A transition of a Turing machine: read `a` in state `q`, write `a'`, move `d`,
enter state `q'`. -/
structure Trans where
  q : ℕ
  a : Sym
  q' : ℕ
  a' : Sym
  d : Dir
deriving DecidableEq

instance : Inhabited Trans := ⟨⟨0, none, 0, none, Dir.stay⟩⟩

namespace NTM

variable (M : NTM)

/-- The list of all transitions of `M`. -/
def transList : List Trans :=
  (List.range M.numStates).flatMap fun q =>
    allSyms.flatMap fun a => (M.step q a).map fun r => ⟨q, a, r.1, r.2.1, r.2.2⟩

theorem mem_transList {tr : Trans} :
    tr ∈ M.transList ↔ tr.q < M.numStates ∧ (tr.q', tr.a', tr.d) ∈ M.step tr.q tr.a := by
  constructor
  · intro h
    simp only [transList, List.mem_flatMap, List.mem_map, List.mem_range] at h
    obtain ⟨q, hq, a, -, r, hr, rfl⟩ := h
    exact ⟨hq, hr⟩
  · rintro ⟨hq, hstep⟩
    simp only [transList, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨tr.q, hq, tr.a, mem_allSyms _, (tr.q', tr.a', tr.d), hstep, by cases tr; rfl⟩

/-- The `j`-th transition of `M` (junk value if `j` is out of range). -/
def trAt (j : ℕ) : Trans := M.transList.getD j default

theorem trAt_mem {j : ℕ} (hj : j < M.transList.length) : M.trAt j ∈ M.transList := by
  rw [trAt, List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem exists_trAt {tr : Trans} (h : tr ∈ M.transList) :
    ∃ j, j < M.transList.length ∧ M.trAt j = tr := by
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.1 h
  exact ⟨j, hj, by rw [trAt, List.getD_eq_getElem _ _ hj, hget]⟩

end NTM

/-! ### The clause groups -/

variable (M : NTM) (x : List Bool) (T : ℕ)

/-- Exactly one state at each time. -/
def stateClauses : CNF TVar :=
  (List.range (T + 1)).flatMap fun t => exactlyOne ((List.range M.numStates).map (TVar.st t))

/-- Exactly one head position at each time. -/
def headClauses : CNF TVar :=
  (List.range (T + 1)).flatMap fun t => exactlyOne ((List.range (T + 1)).map (TVar.hd t))

/-- Exactly one symbol in each cell at each time. -/
def cellClauses : CNF TVar :=
  (List.range (T + 1)).flatMap fun t =>
    (List.range (T + 1)).flatMap fun i => exactlyOne (allSyms.map (TVar.cell t i))

/-- The initial configuration. -/
def initClauses : CNF TVar :=
  [(TVar.st 0 M.start, true)] :: [(TVar.hd 0 0, true)] ::
    (List.range (T + 1)).map fun i => [(TVar.cell 0 i x[i]?, true)]

/-- The accepting state is visited. -/
def acceptClauses : CNF TVar :=
  [atLeastOne ((List.range (T + 1)).map fun t => TVar.st t M.accept)]

/-- Before the last time step the head is not at the last cell (it cannot be, since it
starts at `0` and moves by at most one cell per step). -/
def headBoundClauses : CNF TVar :=
  (List.range T).map fun t => [(TVar.hd t T, false)]

/-- The transition clauses. -/
def transClauses : CNF TVar :=
  ((List.range T).map fun t =>
      atLeastOne ((List.range M.transList.length).map (TVar.mv t))) ++
  ((List.range T).flatMap fun t =>
    (List.range M.transList.length).flatMap fun j =>
      [ implClause [TVar.mv t j] (TVar.st t (M.trAt j).q),
        implClause [TVar.mv t j] (TVar.st (t + 1) (M.trAt j).q') ] ++
      ((List.range (T + 1)).flatMap fun i =>
        [ implClause [TVar.mv t j, TVar.hd t i] (TVar.cell t i (M.trAt j).a),
          implClause [TVar.mv t j, TVar.hd t i] (TVar.cell (t + 1) i (M.trAt j).a'),
          implClause [TVar.mv t j, TVar.hd t i] (TVar.hd (t + 1) ((M.trAt j).d.move i)) ]))

/-- Cells away from the head do not change. -/
def inertiaClauses : CNF TVar :=
  (List.range T).flatMap fun t =>
    (List.range (T + 1)).flatMap fun i =>
      (List.range (T + 1)).flatMap fun k =>
        if k = i then [] else
          allSyms.map fun a =>
            implClause [TVar.hd t i, TVar.cell t k a] (TVar.cell (t + 1) k a)

/-- The Cook–Levin tableau formula for machine `M`, input `x` and time bound `T`. -/
def tableau : CNF TVar :=
  stateClauses M T ++ headClauses T ++ cellClauses T ++ initClauses M x T ++
    acceptClauses M T ++ headBoundClauses T ++ transClauses M T ++ inertiaClauses T

variable {M x T}

theorem eval_tableau_iff (σ : TVar → Bool) :
    CNF.eval σ (tableau M x T) = true ↔
      CNF.eval σ (stateClauses M T) = true ∧ CNF.eval σ (headClauses T) = true ∧
      CNF.eval σ (cellClauses T) = true ∧ CNF.eval σ (initClauses M x T) = true ∧
      CNF.eval σ (acceptClauses M T) = true ∧ CNF.eval σ (headBoundClauses T) = true ∧
      CNF.eval σ (transClauses M T) = true ∧ CNF.eval σ (inertiaClauses T) = true := by
  simp only [tableau, CNF.eval_append, Bool.and_eq_true, and_assoc]

/-! ### Semantics of the individual clause groups -/

variable (σ : TVar → Bool)

theorem eval_stateClauses_iff :
    CNF.eval σ (stateClauses M T) = true ↔
      ∀ t ≤ T, (∃ q, q < M.numStates ∧ σ (TVar.st t q) = true) ∧
        ∀ q < M.numStates, ∀ q' < M.numStates,
          σ (TVar.st t q) = true → σ (TVar.st t q') = true → q = q' := by
  simp [stateClauses, eval_flatMap, eval_exactlyOne]

theorem eval_headClauses_iff :
    CNF.eval σ (headClauses T) = true ↔
      ∀ t ≤ T, (∃ i, i ≤ T ∧ σ (TVar.hd t i) = true) ∧
        ∀ i ≤ T, ∀ i' ≤ T, σ (TVar.hd t i) = true → σ (TVar.hd t i') = true → i = i' := by
  simp [headClauses, eval_flatMap, eval_exactlyOne]

theorem eval_cellClauses_iff :
    CNF.eval σ (cellClauses T) = true ↔
      ∀ t ≤ T, ∀ i ≤ T, (∃ a : Sym, σ (TVar.cell t i a) = true) ∧
        ∀ a b : Sym, σ (TVar.cell t i a) = true → σ (TVar.cell t i b) = true → a = b := by
  simp [cellClauses, eval_flatMap, eval_exactlyOne]

theorem eval_initClauses_iff :
    CNF.eval σ (initClauses M x T) = true ↔
      σ (TVar.st 0 M.start) = true ∧ σ (TVar.hd 0 0) = true ∧
        ∀ i ≤ T, σ (TVar.cell 0 i x[i]?) = true := by
  simp [initClauses, eval_iff, CNF.Clause.eval]

theorem eval_acceptClauses_iff :
    CNF.eval σ (acceptClauses M T) = true ↔
      ∃ t, t ≤ T ∧ σ (TVar.st t M.accept) = true := by
  simp [acceptClauses, eval_atLeastOne]

theorem eval_headBoundClauses_iff :
    CNF.eval σ (headBoundClauses T) = true ↔ ∀ t < T, σ (TVar.hd t T) = false := by
  simp [headBoundClauses, eval_iff, CNF.Clause.eval]

theorem eval_transClauses_iff :
    CNF.eval σ (transClauses M T) = true ↔
      (∀ t < T, ∃ j, j < M.transList.length ∧ σ (TVar.mv t j) = true) ∧
      (∀ t < T, ∀ j < M.transList.length, σ (TVar.mv t j) = true →
        σ (TVar.st t (M.trAt j).q) = true ∧ σ (TVar.st (t + 1) (M.trAt j).q') = true ∧
        ∀ i ≤ T, σ (TVar.hd t i) = true →
          σ (TVar.cell t i (M.trAt j).a) = true ∧
          σ (TVar.cell (t + 1) i (M.trAt j).a') = true ∧
          σ (TVar.hd (t + 1) ((M.trAt j).d.move i)) = true) := by
  simp only [transClauses, CNF.eval_append, Bool.and_eq_true, eval_map_singleton,
    eval_flatMap, List.mem_range, Nat.lt_succ_iff, eval_atLeastOne_map,
    CNF.eval_cons, CNF.eval_nil, Bool.and_true, eval_implClause, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨hA, fun t ht j hj hmv => ?_⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hB t ht j hj
    exact ⟨h1 hmv, h2 hmv, fun i hi hhd =>
      ⟨(h3 i hi).1 ⟨hmv, hhd⟩, (h3 i hi).2.1 ⟨hmv, hhd⟩, (h3 i hi).2.2 ⟨hmv, hhd⟩⟩⟩
  · rintro ⟨hA, hB⟩
    refine ⟨hA, fun t ht j hj =>
      ⟨⟨fun hmv => (hB t ht j hj hmv).1, fun hmv => (hB t ht j hj hmv).2.1⟩,
       fun i hi => ⟨fun h => ((hB t ht j hj h.1).2.2 i hi h.2).1,
         fun h => ((hB t ht j hj h.1).2.2 i hi h.2).2.1,
         fun h => ((hB t ht j hj h.1).2.2 i hi h.2).2.2⟩⟩⟩

theorem eval_inertiaClauses_iff :
    CNF.eval σ (inertiaClauses T) = true ↔
      ∀ t < T, ∀ i ≤ T, ∀ k ≤ T, k ≠ i → ∀ a : Sym,
        σ (TVar.hd t i) = true → σ (TVar.cell t k a) = true →
          σ (TVar.cell (t + 1) k a) = true := by
  simp only [inertiaClauses, eval_flatMap, List.mem_range, Nat.lt_succ_iff]
  constructor
  · intro h t ht i hi k hk hne a hhd hcell
    have h1 := h t ht i hi k hk
    rw [if_neg hne, eval_map_singleton] at h1
    have h2 := h1 a (mem_allSyms a)
    rw [eval_implClause] at h2
    exact h2 (by simp [hhd, hcell])
  · intro h t ht i hi k hk
    by_cases hne : k = i
    · simp [hne]
    · rw [if_neg hne, eval_map_singleton]
      intro a _
      rw [eval_implClause]
      intro hall
      exact h t ht i hi k hk hne a (hall _ (by simp)) (hall _ (by simp))

end Frontier

