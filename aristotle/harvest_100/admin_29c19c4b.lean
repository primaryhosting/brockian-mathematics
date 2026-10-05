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
def Lit.eval {V : Type} (a : V → Bool) (l : Lit V) : Bool :=
  if l.pol then a l.var else !a l.var

/-- Value of a clause under an assignment. -/
def Clause.eval {V : Type} (a : V → Bool) (c : Clause V) : Bool :=
  c.any (Lit.eval a)

/-- Value of a CNF formula under an assignment. -/
def CNF.eval {V : Type} (a : V → Bool) (φ : CNF V) : Bool :=
  φ.all (Clause.eval a)

/-- A CNF formula is satisfiable if some assignment makes it true. -/
def Satisfiable {V : Type} (φ : CNF V) : Prop := ∃ a : V → Bool, CNF.eval a φ = true

/-- The size of a CNF formula: number of clauses plus number of literal occurrences. -/
def CNF.size {V : Type} (φ : CNF V) : Nat := φ.length + (φ.map List.length).sum

theorem CNF.eval_eq_true_iff {V : Type} (a : V → Bool) (φ : CNF V) :
    CNF.eval a φ = true ↔ ∀ c ∈ φ, Clause.eval a c = true := by
  simp [CNF.eval, List.all_eq_true]

theorem Clause.eval_eq_true_iff {V : Type} (a : V → Bool) (c : Clause V) :
    Clause.eval a c = true ↔ ∃ l ∈ c, Lit.eval a l = true := by
  simp [Clause.eval, List.any_eq_true]

theorem CNF.eval_append {V : Type} (a : V → Bool) (φ ψ : CNF V) :
    CNF.eval a (φ ++ ψ) = true ↔ CNF.eval a φ = true ∧ CNF.eval a ψ = true := by
  simp only [CNF.eval_eq_true_iff, List.mem_append]
  constructor
  · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨h1, h2⟩ c (hc | hc)
    · exact h1 c hc
    · exact h2 c hc

/-- Rename the variables of a literal. -/
def Lit.map {V W : Type} (f : V → W) (l : Lit V) : Lit W := ⟨f l.var, l.pol⟩

/-- Rename the variables of a CNF formula. -/
def CNF.rename {V W : Type} (f : V → W) (φ : CNF V) : CNF W :=
  φ.map (List.map (Lit.map f))

theorem CNF.size_rename {V W : Type} (f : V → W) (φ : CNF V) :
    (CNF.rename f φ).size = φ.size := by
  simp [CNF.size, CNF.rename, List.map_map, Function.comp_def]

/-- Satisfiability is invariant under injective renaming of variables. -/
theorem Lit.eval_map {V W : Type} {f : V → W} {a : V → Bool} {b : W → Bool}
    (h : ∀ v, b (f v) = a v) (l : Lit V) : Lit.eval b (Lit.map f l) = Lit.eval a l := by
  simp [Lit.eval, Lit.map, h]

theorem Clause.eval_map {V W : Type} {f : V → W} {a : V → Bool} {b : W → Bool}
    (h : ∀ v, b (f v) = a v) (c : Clause V) :
    Clause.eval b (List.map (Lit.map f) c) = Clause.eval a c := by
  simp [Clause.eval, List.any_map, Function.comp_def, Lit.eval_map h]

theorem CNF.eval_rename {V W : Type} {f : V → W} {a : V → Bool} {b : W → Bool}
    (h : ∀ v, b (f v) = a v) (φ : CNF V) : CNF.eval b (CNF.rename f φ) = CNF.eval a φ := by
  simp [CNF.eval, CNF.rename, List.all_map, Function.comp_def, Clause.eval_map h]

/-- Satisfiability is invariant under injective renaming of variables. -/
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
def TM.stepCfg {n : Nat} (M : TM n) (c : Cfg n) : Cfg n :=
  { state := (M.step c.state (c.tape c.head)).1
    tape := fun j => if j = c.head then (M.step c.state (c.tape c.head)).2.1 else c.tape j
    head := match (M.step c.state (c.tape c.head)).2.2 with
      | Dir.L => c.head - 1
      | Dir.R => c.head + 1
      | Dir.S => c.head }

/-- Iterating the machine for `t` steps. -/
def TM.run {n : Nat} (M : TM n) : Nat → Cfg n → Cfg n
  | 0, c => c
  | (t + 1), c => M.stepCfg (M.run t c)

/-- The initial configuration on input `u`: the head sits on the blank cell `0`,
and the input occupies cells `1, …, |u|`. -/
def TM.initCfg {n : Nat} (M : TM n) (u : List Bool) : Cfg n :=
  { state := M.start
    tape := fun i => match i with | 0 => none | (j + 1) => u[j]?
    head := 0 }

/-- `M` accepts `u` within `T` steps. -/
def TM.Accepts {n : Nat} (M : TM n) (T : Nat) (u : List Bool) : Prop :=
  ∃ t ≤ T, (M.run t (M.initCfg u)).state = M.accept

/-! ## Cells and the local transition rule -/

/-- A cell of the computation tableau: the tape symbol, together with the state of
the machine if the head is on this cell. -/
abbrev Cell (n : Nat) := Sym × Option (Fin n)

/-- The cell of the tableau at position `i` for configuration `c`. -/
def Cfg.cell {n : Nat} (c : Cfg n) (i : Nat) : Cell n :=
  (c.tape i, if c.head = i then some c.state else none)

/-- State arriving at a cell from its left neighbour. -/
def TM.arriveL {n : Nat} (M : TM n) (a : Cell n) : Option (Fin n) :=
  match a.2 with
  | none => none
  | some q => match M.step q a.1 with
    | (q', _, Dir.R) => some q'
    | _ => none

/-- State arriving at a cell from its right neighbour. -/
def TM.arriveR {n : Nat} (M : TM n) (d : Cell n) : Option (Fin n) :=
  match d.2 with
  | none => none
  | some q => match M.step q d.1 with
    | (q', _, Dir.L) => some q'
    | _ => none

/-- The new content of a cell coming from the cell itself. -/
def TM.selfCell {n : Nat} (M : TM n) (b : Cell n) : Cell n :=
  match b.2 with
  | none => (b.1, none)
  | some q => match M.step q b.1 with
    | (q', s', Dir.S) => (s', some q')
    | (_, s', _) => (s', none)

/-- The local rule of the tableau at an interior cell. -/
def TM.rule {n : Nat} (M : TM n) (a b d : Cell n) : Cell n :=
  ((M.selfCell b).1,
    match (M.selfCell b).2 with
    | some q => some q
    | none => match M.arriveL a with
      | some q => some q
      | none => M.arriveR d)

/-- The local rule at the leftmost cell (position `0`): a left move keeps the head. -/
def TM.ruleL {n : Nat} (M : TM n) (b d : Cell n) : Cell n :=
  match b.2 with
  | none => (b.1, M.arriveR d)
  | some q => match M.step q b.1 with
    | (_, s', Dir.R) => (s', none)
    | (q', s', _) => (s', some q')

/-- The local rule at the rightmost cell of the tableau. -/
def TM.ruleR {n : Nat} (M : TM n) (a b : Cell n) : Cell n := M.rule a b (none, none)

theorem TM.cell_step_interior {n : Nat} (M : TM n) (c : Cfg n) (i : Nat) :
    (M.stepCfg c).cell (i + 1) = M.rule (c.cell i) (c.cell (i + 1)) (c.cell (i + 2)) := by
  obtain ⟨st, tp, hd⟩ := c
  rcases hr : M.step st (tp hd) with ⟨q', s', d⟩
  by_cases h1 : hd = i + 1
  · subst h1
    cases d <;>
      simp [Cfg.cell, TM.stepCfg, TM.rule, TM.selfCell, TM.arriveL, TM.arriveR, hr]
  · by_cases h2 : hd = i
    · subst h2
      cases d <;>
        simp [Cfg.cell, TM.stepCfg, TM.rule, TM.selfCell, TM.arriveL, TM.arriveR, hr, h1]
    · by_cases h3 : hd = i + 2
      · subst h3
        cases d <;>
          simp [Cfg.cell, TM.stepCfg, TM.rule, TM.selfCell, TM.arriveL, TM.arriveR, hr, h1, h2]
      · cases d <;>
          simp [Cfg.cell, TM.stepCfg, TM.rule, TM.selfCell, TM.arriveL, TM.arriveR, hr, h1, h2,
            h3] <;> omega

theorem TM.cell_step_zero {n : Nat} (M : TM n) (c : Cfg n) :
    (M.stepCfg c).cell 0 = M.ruleL (c.cell 0) (c.cell 1) := by
  obtain ⟨st, tp, hd⟩ := c
  rcases hr : M.step st (tp hd) with ⟨q', s', d⟩
  by_cases h1 : hd = 0
  · subst h1
    cases d <;>
      simp [Cfg.cell, TM.stepCfg, TM.ruleL, TM.arriveR, hr]
  · by_cases h2 : hd = 1
    · subst h2
      cases d <;>
        simp [Cfg.cell, TM.stepCfg, TM.ruleL, TM.arriveR, hr, h1]
    · cases d <;>
        simp [Cfg.cell, TM.stepCfg, TM.ruleL, TM.arriveR, hr, h1, h2] <;> omega

/-! ## The tableau encoding

Given a machine `M`, a time bound `T`, an input `x` and a witness length `m`, we build a
CNF formula whose variables are triples `(t, i, s)` meaning "at time `t` the cell at
position `i` of the tableau has content `s`".
-/

/-- Variables of the tableau formula. -/
abbrev TVar (n : Nat) := Nat × Nat × Cell n

/-- All tape symbols. -/
def symList : List Sym := [none, some false, some true]

theorem mem_symList (s : Sym) : s ∈ symList := by
  cases s with
  | none => simp [symList]
  | some b => cases b <;> simp [symList]

/-- All possible cell contents. -/
def cellList (n : Nat) : List (Cell n) :=
  symList.flatMap fun γ => (none :: (List.finRange n).map some).map fun h => (γ, h)

theorem mem_cellList {n : Nat} (s : Cell n) : s ∈ cellList n := by
  obtain ⟨γ, h⟩ := s
  refine List.mem_flatMap.mpr ⟨γ, mem_symList γ, ?_⟩
  refine List.mem_map.mpr ⟨h, ?_, rfl⟩
  cases h with
  | none => simp
  | some q => exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_finRange q))

/-- Width of the tableau: the number of tape cells that are tracked. -/
def tabWidth (T : Nat) (x : List Bool) (m : Nat) : Nat := x.length + m + T + 3

/-- Clauses saying that every tracked cell has exactly one content. -/
def cellClauses (n T Wd : Nat) : CNF (TVar n) :=
  (List.range (T + 1)).flatMap fun t => (List.range Wd).flatMap fun i =>
    ((cellList n).map fun s => (⟨(t, i, s), true⟩ : Lit (TVar n))) ::
      ((cellList n).flatMap fun s => (cellList n).filterMap fun s' =>
        if s = s' then none
        else some [(⟨(t, i, s), false⟩ : Lit (TVar n)), ⟨(t, i, s'), false⟩])

/-- Clauses describing the initial row: the head is on cell `0` in the start state, the
input occupies cells `1, …, |x|`, the witness cells `|x|+1, …, |x|+m` carry an arbitrary
bit, and the remaining cells are blank. -/
def initClauses {n : Nat} (M : TM n) (T : Nat) (x : List Bool) (m : Nat) : CNF (TVar n) :=
  [(⟨(0, 0, ((none : Sym), some M.start)), true⟩ : Lit (TVar n))] ::
    (((List.range x.length).map fun j =>
        [(⟨(0, j + 1, (some (x.getD j false), (none : Option (Fin n)))), true⟩ : Lit (TVar n))]) ++
      ((List.range m).map fun j =>
        [(⟨(0, x.length + 1 + j, (some false, (none : Option (Fin n)))), true⟩ : Lit (TVar n)),
          ⟨(0, x.length + 1 + j, (some true, (none : Option (Fin n)))), true⟩]) ++
      ((List.range (T + 2)).map fun j =>
        [(⟨(0, x.length + m + 1 + j, ((none : Sym), (none : Option (Fin n)))), true⟩ :
          Lit (TVar n))]))

/-- Clauses implementing the local transition rule. -/
def transClauses {n : Nat} (M : TM n) (T Wd : Nat) : CNF (TVar n) :=
  (List.range T).flatMap fun t =>
    ((cellList n).flatMap fun b => (cellList n).map fun d =>
      [(⟨(t, 0, b), false⟩ : Lit (TVar n)), ⟨(t, 1, d), false⟩,
        ⟨(t + 1, 0, M.ruleL b d), true⟩]) ++
    ((List.range (Wd - 2)).flatMap fun i =>
      (cellList n).flatMap fun a => (cellList n).flatMap fun b => (cellList n).map fun d =>
        [(⟨(t, i, a), false⟩ : Lit (TVar n)), ⟨(t, i + 1, b), false⟩, ⟨(t, i + 2, d), false⟩,
          ⟨(t + 1, i + 1, M.rule a b d), true⟩]) ++
    ((cellList n).flatMap fun a => (cellList n).map fun b =>
      [(⟨(t, Wd - 2, a), false⟩ : Lit (TVar n)), ⟨(t, Wd - 1, b), false⟩,
        ⟨(t + 1, Wd - 1, M.ruleR a b), true⟩])

/-- The clause saying that the accepting state occurs somewhere in the tableau. -/
def acceptClause {n : Nat} (M : TM n) (T Wd : Nat) : Clause (TVar n) :=
  (List.range (T + 1)).flatMap fun t => (List.range Wd).flatMap fun i =>
    symList.map fun γ => (⟨(t, i, (γ, some M.accept)), true⟩ : Lit (TVar n))

/-- The tableau formula for machine `M`, time bound `T`, input `x` and witness length `m`. -/
def tableau {n : Nat} (M : TM n) (T : Nat) (x : List Bool) (m : Nat) : CNF (TVar n) :=
  cellClauses n T (tabWidth T x m) ++ initClauses M T x m ++
    transClauses M T (tabWidth T x m) ++ [acceptClause M T (tabWidth T x m)]

/-! ## Basic facts about runs -/

theorem TM.head_run_le {n : Nat} (M : TM n) (c : Cfg n) (t : Nat) :
    (M.run t c).head ≤ c.head + t := by
  induction t with
  | zero => simp [TM.run]
  | succ t ih =>
    have : (M.stepCfg (M.run t c)).head ≤ (M.run t c).head + 1 := by
      simp only [TM.stepCfg]
      cases (M.step (M.run t c).state ((M.run t c).tape (M.run t c).head)).2.2 <;>
        simp <;> omega
    simp only [TM.run]
    omega

theorem TM.head_run_initCfg_le {n : Nat} (M : TM n) (u : List Bool) (t : Nat) :
    (M.run t (M.initCfg u)).head ≤ t := by
  have := M.head_run_le (M.initCfg u) t
  simpa [TM.initCfg] using this

theorem TM.tape_run_far {n : Nat} (M : TM n) (u : List Bool) (t i : Nat)
    (h1 : u.length + 1 ≤ i) (h2 : t < i) : (M.run t (M.initCfg u)).tape i = none := by
  induction t with
  | zero =>
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [TM.run, TM.initCfg]
    exact List.getElem?_eq_none (by omega)
  | succ t ih =>
    have hlt : (M.run t (M.initCfg u)).head < i := by
      have := M.head_run_initCfg_le u t
      omega
    have := ih (by omega)
    simp only [TM.run, TM.stepCfg]
    rw [if_neg (by omega)]
    exact this

theorem TM.cell_run_far {n : Nat} (M : TM n) (u : List Bool) (t i : Nat)
    (h1 : u.length + 1 ≤ i) (h2 : t < i) :
    (M.run t (M.initCfg u)).cell i = ((none : Sym), (none : Option (Fin n))) := by
  have h3 : (M.run t (M.initCfg u)).head < i := by
    have := M.head_run_initCfg_le u t
    omega
  simp [Cfg.cell, M.tape_run_far u t i h1 h2, Nat.ne_of_lt h3]

theorem TM.cell_initCfg_zero {n : Nat} (M : TM n) (u : List Bool) :
    (M.initCfg u).cell 0 = ((none : Sym), some M.start) := by
  simp [Cfg.cell, TM.initCfg]

theorem TM.cell_initCfg_succ {n : Nat} (M : TM n) (u : List Bool) (j : Nat) :
    (M.initCfg u).cell (j + 1) = (u[j]?, (none : Option (Fin n))) := by
  simp [Cfg.cell, TM.initCfg]

/-- The intended value of the tableau cell at time `t` and position `i`. -/
def tabRow {n : Nat} (M : TM n) (u : List Bool) (t i : Nat) : Cell n :=
  (M.run t (M.initCfg u)).cell i

theorem tabRow_zero {n : Nat} (M : TM n) (u : List Bool) (i : Nat) :
    tabRow M u 0 i = (M.initCfg u).cell i := rfl

theorem tabRow_step_interior {n : Nat} (M : TM n) (u : List Bool) (t i : Nat) :
    tabRow M u (t + 1) (i + 1) =
      M.rule (tabRow M u t i) (tabRow M u t (i + 1)) (tabRow M u t (i + 2)) :=
  M.cell_step_interior _ i

theorem tabRow_step_zero {n : Nat} (M : TM n) (u : List Bool) (t : Nat) :
    tabRow M u (t + 1) 0 = M.ruleL (tabRow M u t 0) (tabRow M u t 1) :=
  M.cell_step_zero _

theorem tabRow_far {n : Nat} (M : TM n) (u : List Bool) (t i : Nat)
    (h1 : u.length + 1 ≤ i) (h2 : t < i) : tabRow M u t i = ((none : Sym), none) :=
  M.cell_run_far u t i h1 h2

/-- The canonical assignment associated with the run of `M` on `u`. -/
def tabAssign {n : Nat} (M : TM n) (u : List Bool) : TVar n → Bool :=
  fun v => decide (tabRow M u v.1 v.2.1 = v.2.2)

theorem tabAssign_pos {n : Nat} (M : TM n) (u : List Bool) (t i : Nat) (s : Cell n)
    (h : tabRow M u t i = s) :
    Lit.eval (tabAssign M u) (⟨(t, i, s), true⟩ : Lit (TVar n)) = true := by
  simp [Lit.eval, tabAssign, h]

theorem tabAssign_neg {n : Nat} (M : TM n) (u : List Bool) (t i : Nat) (s : Cell n)
    (h : tabRow M u t i ≠ s) :
    Lit.eval (tabAssign M u) (⟨(t, i, s), false⟩ : Lit (TVar n)) = true := by
  simp [Lit.eval, tabAssign, h]

/-! ## Correctness of the encoding -/

theorem satisfiable_tableau_of_accepts {n : Nat} (M : TM n) (T : Nat) (x : List Bool) (m : Nat)
    (w : List Bool) (hw : w.length = m) (hacc : M.Accepts T (x ++ w)) :
    Satisfiable (tableau M T x m) := by
  classical
  refine ⟨tabAssign M (x ++ w), ?_⟩
  have hneg := tabAssign_neg M (x ++ w)
  have hpos := tabAssign_pos M (x ++ w)
  have hlen : (x ++ w).length = x.length + m := by simp [hw]
  rw [tableau, CNF.eval_append, CNF.eval_append, CNF.eval_append]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- exactly-one clauses
    rw [CNF.eval_eq_true_iff]
    intro c hc
    simp only [cellClauses, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.mem_filterMap] at hc
    obtain ⟨t, ht, i, hi, hc⟩ := hc
    rcases hc with rfl | ⟨s, -, s', -, hc⟩
    · rw [Clause.eval_eq_true_iff]
      exact ⟨⟨(t, i, tabRow M (x ++ w) t i), true⟩, List.mem_map_of_mem (mem_cellList _),
        hpos t i _ rfl⟩
    · by_cases hss : s = s'
      · simp [hss] at hc
      · rw [if_neg hss] at hc
        have hc' : c = [(⟨(t, i, s), false⟩ : Lit (TVar n)), ⟨(t, i, s'), false⟩] :=
          (Option.some.inj hc).symm
        subst hc'
        rw [Clause.eval_eq_true_iff]
        by_cases h : tabRow M (x ++ w) t i = s
        · exact ⟨⟨(t, i, s'), false⟩, by simp, hneg t i s' (by rw [h]; exact hss)⟩
        · exact ⟨⟨(t, i, s), false⟩, by simp, hneg t i s h⟩
  · -- initial row
    rw [CNF.eval_eq_true_iff]
    intro c hc
    simp only [initClauses, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hc
    rcases hc with rfl | (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
    · rw [Clause.eval_eq_true_iff]
      refine ⟨⟨(0, 0, ((none : Sym), some M.start)), true⟩, by simp, hpos 0 0 _ ?_⟩
      rw [tabRow_zero, M.cell_initCfg_zero]
    · rw [Clause.eval_eq_true_iff]
      refine ⟨⟨(0, j + 1, (some (x.getD j false), (none : Option (Fin n)))), true⟩, by simp,
        hpos 0 (j + 1) _ ?_⟩
      have hval : (x ++ w)[j]? = some (x.getD j false) := by
        rw [List.getElem?_append_left hj]
        simp [List.getD, List.getElem?_eq_getElem hj]
      rw [tabRow_zero, M.cell_initCfg_succ, hval]
    · rw [Clause.eval_eq_true_iff]
      have hidx : x.length + 1 + j = (x.length + j) + 1 := by omega
      have hval : (x ++ w)[x.length + j]? = some (w.getD j false) := by
        rw [List.getElem?_append_right (by omega)]
        have hj' : j < w.length := by omega
        simp [List.getD, List.getElem?_eq_getElem hj']
      have hrow : tabRow M (x ++ w) 0 (x.length + 1 + j) =
          (some (w.getD j false), (none : Option (Fin n))) := by
        rw [hidx, tabRow_zero, M.cell_initCfg_succ, hval]
      cases hb : w.getD j false
      · exact ⟨⟨(0, x.length + 1 + j, (some false, (none : Option (Fin n)))), true⟩, by simp,
          hpos 0 _ _ (by rw [hrow, hb])⟩
      · exact ⟨⟨(0, x.length + 1 + j, (some true, (none : Option (Fin n)))), true⟩, by simp,
          hpos 0 _ _ (by rw [hrow, hb])⟩
    · rw [Clause.eval_eq_true_iff]
      refine ⟨⟨(0, x.length + m + 1 + j, ((none : Sym), (none : Option (Fin n)))), true⟩, by simp,
        hpos 0 (x.length + m + 1 + j) _ ?_⟩
      have hidx : x.length + m + 1 + j = (x.length + m + j) + 1 := by omega
      rw [hidx, tabRow_zero, M.cell_initCfg_succ, List.getElem?_eq_none (by omega)]
  · -- transition clauses
    rw [CNF.eval_eq_true_iff]
    intro c hc
    simp only [transClauses, List.mem_flatMap, List.mem_range, List.mem_append,
      List.mem_map] at hc
    obtain ⟨t, ht, hc⟩ := hc
    rcases hc with (hc | hc) | hc
    · obtain ⟨b, -, d, -, rfl⟩ := hc
      rw [Clause.eval_eq_true_iff]
      by_cases hb : tabRow M (x ++ w) t 0 = b
      · by_cases hd : tabRow M (x ++ w) t 1 = d
        · exact ⟨⟨(t + 1, 0, M.ruleL b d), true⟩, by simp,
            hpos (t + 1) 0 _ (by rw [tabRow_step_zero, hb, hd])⟩
        · exact ⟨⟨(t, 1, d), false⟩, by simp, hneg t 1 d hd⟩
      · exact ⟨⟨(t, 0, b), false⟩, by simp, hneg t 0 b hb⟩
    · obtain ⟨i, -, a, -, b, -, d, -, rfl⟩ := hc
      rw [Clause.eval_eq_true_iff]
      by_cases ha : tabRow M (x ++ w) t i = a
      · by_cases hb : tabRow M (x ++ w) t (i + 1) = b
        · by_cases hd : tabRow M (x ++ w) t (i + 2) = d
          · exact ⟨⟨(t + 1, i + 1, M.rule a b d), true⟩, by simp,
              hpos (t + 1) (i + 1) _ (by rw [tabRow_step_interior, ha, hb, hd])⟩
          · exact ⟨⟨(t, i + 2, d), false⟩, by simp, hneg t (i + 2) d hd⟩
        · exact ⟨⟨(t, i + 1, b), false⟩, by simp, hneg t (i + 1) b hb⟩
      · exact ⟨⟨(t, i, a), false⟩, by simp, hneg t i a ha⟩
    · obtain ⟨a, -, b, -, rfl⟩ := hc
      rw [Clause.eval_eq_true_iff]
      have hW2 : tabWidth T x m - 2 = x.length + m + T + 1 := by simp only [tabWidth]; omega
      have hW1 : tabWidth T x m - 1 = x.length + m + T + 2 := by simp only [tabWidth]; omega
      by_cases ha : tabRow M (x ++ w) t (tabWidth T x m - 2) = a
      · by_cases hb : tabRow M (x ++ w) t (tabWidth T x m - 1) = b
        · refine ⟨⟨(t + 1, tabWidth T x m - 1, M.ruleR a b), true⟩, by simp,
            hpos (t + 1) (tabWidth T x m - 1) _ ?_⟩
          have hfar : tabRow M (x ++ w) t (x.length + m + T + 3) =
              ((none : Sym), (none : Option (Fin n))) :=
            tabRow_far M (x ++ w) t _ (by omega) (by omega)
          have hstep : tabRow M (x ++ w) (t + 1) (x.length + m + T + 2) =
              M.rule (tabRow M (x ++ w) t (x.length + m + T + 1))
                (tabRow M (x ++ w) t (x.length + m + T + 2))
                (tabRow M (x ++ w) t (x.length + m + T + 3)) :=
            tabRow_step_interior M (x ++ w) t (x.length + m + T + 1)
          rw [hW1] at hb ⊢
          rw [hW2] at ha
          rw [hstep, ha, hb, hfar]
          rfl
        · exact ⟨⟨(t, tabWidth T x m - 1, b), false⟩, by simp, hneg t _ b hb⟩
      · exact ⟨⟨(t, tabWidth T x m - 2, a), false⟩, by simp, hneg t _ a ha⟩
  · -- acceptance clause
    rw [CNF.eval_eq_true_iff]
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    obtain ⟨t0, ht0, hst⟩ := hacc
    rw [Clause.eval_eq_true_iff]
    have hhead : (M.run t0 (M.initCfg (x ++ w))).head ≤ t0 := M.head_run_initCfg_le (x ++ w) t0
    refine ⟨⟨(t0, (M.run t0 (M.initCfg (x ++ w))).head,
      ((M.run t0 (M.initCfg (x ++ w))).tape (M.run t0 (M.initCfg (x ++ w))).head,
        some M.accept)), true⟩, ?_, ?_⟩
    · refine List.mem_flatMap.mpr ⟨t0, List.mem_range.mpr (by omega), ?_⟩
      refine List.mem_flatMap.mpr ⟨(M.run t0 (M.initCfg (x ++ w))).head,
        List.mem_range.mpr ?_, ?_⟩
      · simp only [tabWidth]; omega
      · exact List.mem_map_of_mem (mem_symList _)
    · refine hpos t0 _ _ ?_
      simp [tabRow, Cfg.cell, hst]

/-- The cell content selected by an assignment at time `t` and position `i`. -/
def pick {n : Nat} (A : TVar n → Bool) (t i : Nat) : Cell n :=
  ((cellList n).find? fun s => A (t, i, s)).getD ((none : Sym), (none : Option (Fin n)))

theorem mem_cellClauses_atLeastOne {n : Nat} (T Wd t i : Nat) (ht : t ≤ T) (hi : i < Wd) :
    ((cellList n).map fun s => (⟨(t, i, s), true⟩ : Lit (TVar n))) ∈ cellClauses n T Wd :=
  List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (by omega),
    List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_cons_self⟩⟩

theorem mem_cellClauses_atMostOne {n : Nat} (T Wd t i : Nat) (ht : t ≤ T) (hi : i < Wd)
    (s s' : Cell n) (hss : s ≠ s') :
    [(⟨(t, i, s), false⟩ : Lit (TVar n)), ⟨(t, i, s'), false⟩] ∈ cellClauses n T Wd :=
  List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (by omega),
    List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
      List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨s, mem_cellList s,
        List.mem_filterMap.mpr ⟨s', mem_cellList s', by rw [if_neg hss]⟩⟩)⟩⟩

theorem pick_spec {n : Nat} (A : TVar n → Bool) (T Wd t i : Nat)
    (hcell : CNF.eval A (cellClauses n T Wd) = true) (ht : t ≤ T) (hi : i < Wd) :
    A (t, i, pick A t i) = true := by
  have hcl := (CNF.eval_eq_true_iff _ _).mp hcell _ (mem_cellClauses_atLeastOne T Wd t i ht hi)
  rw [Clause.eval_eq_true_iff] at hcl
  obtain ⟨l, hl, hlv⟩ := hcl
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl
  have hAs : A (t, i, s) = true := by simpa [Lit.eval] using hlv
  unfold pick
  cases hf : (cellList n).find? (fun s => A (t, i, s)) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd hAs (by simpa using hf s hs)
  | some s0 =>
    have := List.find?_some hf
    simpa using this

theorem pick_uniq {n : Nat} (A : TVar n → Bool) (T Wd t i : Nat)
    (hcell : CNF.eval A (cellClauses n T Wd) = true) (ht : t ≤ T) (hi : i < Wd)
    (s : Cell n) (hs : A (t, i, s) = true) : s = pick A t i := by
  refine Classical.byContradiction fun hne => ?_
  have hcl := (CNF.eval_eq_true_iff _ _).mp hcell _
    (mem_cellClauses_atMostOne T Wd t i ht hi s (pick A t i) hne)
  rw [Clause.eval_eq_true_iff] at hcl
  obtain ⟨l, hl, hlv⟩ := hcl
  have hp := pick_spec A T Wd t i hcell ht hi
  rcases List.mem_cons.mp hl with rfl | hl
  · simp [Lit.eval, hs] at hlv
  · rcases List.mem_cons.mp hl with rfl | hl
    · simp [Lit.eval, hp] at hlv
    · simp at hl

/-- The witness read off from the initial row of an assignment. -/
def pickWitness {n : Nat} (A : TVar n → Bool) (x : List Bool) (m : Nat) : List Bool :=
  (List.range m).map fun j => ((pick A 0 (x.length + 1 + j)).1).getD false

theorem pickWitness_length {n : Nat} (A : TVar n → Bool) (x : List Bool) (m : Nat) :
    (pickWitness A x m).length = m := by simp [pickWitness]

theorem pickWitness_getD {n : Nat} (A : TVar n → Bool) (x : List Bool) (m j : Nat)
    (hj : j < m) :
    (pickWitness A x m).getD j false = ((pick A 0 (x.length + 1 + j)).1).getD false := by
  have hj' : j < (pickWitness A x m).length := by rw [pickWitness_length]; exact hj
  rw [List.getD, List.getElem?_eq_getElem hj']
  simp [pickWitness]

theorem pick_eq_tabRow_zero {n : Nat} (M : TM n) (T : Nat) (x : List Bool) (m : Nat)
    (A : TVar n → Bool)
    (hcell : CNF.eval A (cellClauses n T (tabWidth T x m)) = true)
    (hinit : CNF.eval A (initClauses M T x m) = true) :
    ∀ i, i < tabWidth T x m → pick A 0 i = tabRow M (x ++ pickWitness A x m) 0 i := by
  have hulen : (x ++ pickWitness A x m).length = x.length + m := by
    simp [pickWitness_length]
  intro i hi
  rw [tabRow_zero]
  by_cases h0 : i = 0
  · subst h0
    have hcl := (CNF.eval_eq_true_iff _ _).mp hinit _ (List.mem_cons_self)
    rw [Clause.eval_eq_true_iff] at hcl
    obtain ⟨l, hl, hlv⟩ := hcl
    rw [List.mem_singleton] at hl
    subst hl
    have hAv : A (0, 0, ((none : Sym), some M.start)) = true := by simpa [Lit.eval] using hlv
    rw [M.cell_initCfg_zero]
    exact (pick_uniq A T (tabWidth T x m) 0 0 hcell (by omega) hi _ hAv).symm
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [M.cell_initCfg_succ]
    by_cases h1 : j < x.length
    · have hcl := (CNF.eval_eq_true_iff _ _).mp hinit _
        (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_map_of_mem (List.mem_range.mpr h1)))))
      rw [Clause.eval_eq_true_iff] at hcl
      obtain ⟨l, hl, hlv⟩ := hcl
      rw [List.mem_singleton] at hl
      subst hl
      have hAv : A (0, j + 1, (some (x.getD j false), (none : Option (Fin n)))) = true := by
        simpa [Lit.eval] using hlv
      have hval : (x ++ pickWitness A x m)[j]? = some (x.getD j false) := by
        rw [List.getElem?_append_left h1]
        simp [List.getD, List.getElem?_eq_getElem h1]
      rw [hval]
      exact (pick_uniq A T (tabWidth T x m) 0 (j + 1) hcell (by omega) hi _ hAv).symm
    · by_cases h2 : j < x.length + m
      · obtain ⟨jj, rfl⟩ : ∃ jj, j = x.length + jj := ⟨j - x.length, by omega⟩
        have hjj : jj < m := by omega
        have hidx : x.length + jj + 1 = x.length + 1 + jj := by omega
        have hcl := (CNF.eval_eq_true_iff _ _).mp hinit _
          (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _
            (List.mem_map_of_mem (List.mem_range.mpr hjj)))))
        rw [Clause.eval_eq_true_iff] at hcl
        obtain ⟨l, hl, hlv⟩ := hcl
        have hpick : ∃ b : Bool, pick A 0 (x.length + 1 + jj) = (some b, (none : Option (Fin n))) := by
          rcases List.mem_cons.mp hl with rfl | hl
          · refine ⟨false, ?_⟩
            have hAv : A (0, x.length + 1 + jj, (some false, (none : Option (Fin n)))) = true := by
              simpa [Lit.eval] using hlv
            exact (pick_uniq A T (tabWidth T x m) 0 (x.length + 1 + jj) hcell (by omega)
              (by omega) _ hAv).symm
          · rcases List.mem_cons.mp hl with rfl | hl
            · refine ⟨true, ?_⟩
              have hAv : A (0, x.length + 1 + jj, (some true, (none : Option (Fin n)))) = true := by
                simpa [Lit.eval] using hlv
              exact (pick_uniq A T (tabWidth T x m) 0 (x.length + 1 + jj) hcell (by omega)
                (by omega) _ hAv).symm
            · simp at hl
        obtain ⟨b, hb⟩ := hpick
        have hbit : (pickWitness A x m).getD jj false = b := by
          rw [pickWitness_getD A x m jj hjj, hb]
          rfl
        have hval : (x ++ pickWitness A x m)[x.length + jj]? = some b := by
          rw [List.getElem?_append_right (by omega)]
          have hjj' : jj < (pickWitness A x m).length := by rw [pickWitness_length]; exact hjj
          have : x.length + jj - x.length = jj := by omega
          rw [this, List.getElem?_eq_getElem hjj']
          have : (pickWitness A x m)[jj] = (pickWitness A x m).getD jj false := by
            rw [List.getD, List.getElem?_eq_getElem hjj']
            rfl
          rw [this, hbit]
        rw [hval, hidx, hb]
      · obtain ⟨jj, rfl⟩ : ∃ jj, j = x.length + m + jj := ⟨j - (x.length + m), by omega⟩
        have hjj : jj < T + 2 := by
          simp only [tabWidth] at hi
          omega
        have hidx : x.length + m + jj + 1 = x.length + m + 1 + jj := by omega
        have hcl := (CNF.eval_eq_true_iff _ _).mp hinit _
          (List.mem_cons_of_mem _ (List.mem_append_right _
            (List.mem_map_of_mem (List.mem_range.mpr hjj))))
        rw [Clause.eval_eq_true_iff] at hcl
        obtain ⟨l, hl, hlv⟩ := hcl
        rw [List.mem_singleton] at hl
        subst hl
        have hAv : A (0, x.length + m + 1 + jj, ((none : Sym), (none : Option (Fin n)))) = true := by
          simpa [Lit.eval] using hlv
        have hval : (x ++ pickWitness A x m)[x.length + m + jj]? = none :=
          List.getElem?_eq_none (by omega)
        rw [hval, hidx]
        exact (pick_uniq A T (tabWidth T x m) 0 (x.length + m + 1 + jj) hcell (by omega)
          (by omega) _ hAv).symm

theorem pick_eq_tabRow_step {n : Nat} (M : TM n) (T : Nat) (x : List Bool) (m : Nat)
    (A : TVar n → Bool)
    (hcell : CNF.eval A (cellClauses n T (tabWidth T x m)) = true)
    (htrans : CNF.eval A (transClauses M T (tabWidth T x m)) = true)
    (t : Nat) (ht : t + 1 ≤ T)
    (ih : ∀ i, i < tabWidth T x m → pick A t i = tabRow M (x ++ pickWitness A x m) t i) :
    ∀ i, i < tabWidth T x m →
      pick A (t + 1) i = tabRow M (x ++ pickWitness A x m) (t + 1) i := by
  have hulen : (x ++ pickWitness A x m).length = x.length + m := by
    simp [pickWitness_length]
  have hWd : tabWidth T x m = x.length + m + T + 3 := rfl
  intro i hi
  by_cases h0 : i = 0
  · subst h0
    have hb := pick_spec A T (tabWidth T x m) t 0 hcell (by omega) (by omega)
    have hd := pick_spec A T (tabWidth T x m) t 1 hcell (by omega) (by omega)
    have hcl := (CNF.eval_eq_true_iff _ _).mp htrans _
      (List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (by omega),
        List.mem_append_left _ (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨pick A t 0, mem_cellList _,
            List.mem_map_of_mem (mem_cellList (pick A t 1))⟩))⟩)
    have hres : A (t + 1, 0, M.ruleL (pick A t 0) (pick A t 1)) = true := by
      simpa [Clause.eval, Lit.eval, hb, hd] using hcl
    have hp := (pick_uniq A T (tabWidth T x m) (t + 1) 0 hcell ht (by omega) _ hres).symm
    rw [hp, ih 0 (by omega), ih 1 (by omega), tabRow_step_zero]
  · obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    by_cases hlast : i0 + 1 = tabWidth T x m - 1
    · -- rightmost column
      have hW2 : tabWidth T x m - 2 = x.length + m + T + 1 := by rw [hWd]; omega
      have hW1 : tabWidth T x m - 1 = x.length + m + T + 2 := by rw [hWd]; omega
      have ha := pick_spec A T (tabWidth T x m) t (tabWidth T x m - 2) hcell (by omega) (by omega)
      have hb := pick_spec A T (tabWidth T x m) t (tabWidth T x m - 1) hcell (by omega) (by omega)
      have hcl := (CNF.eval_eq_true_iff _ _).mp htrans _
        (List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (by omega),
          List.mem_append_right _
            (List.mem_flatMap.mpr ⟨pick A t (tabWidth T x m - 2), mem_cellList _,
              List.mem_map_of_mem (mem_cellList (pick A t (tabWidth T x m - 1)))⟩)⟩)
      have hres : A (t + 1, tabWidth T x m - 1,
          M.ruleR (pick A t (tabWidth T x m - 2)) (pick A t (tabWidth T x m - 1))) = true := by
        simpa [Clause.eval, Lit.eval, ha, hb] using hcl
      have hp := (pick_uniq A T (tabWidth T x m) (t + 1) (tabWidth T x m - 1) hcell ht
        (by omega) _ hres).symm
      have hfar : tabRow M (x ++ pickWitness A x m) t (x.length + m + T + 3) =
          ((none : Sym), (none : Option (Fin n))) :=
        tabRow_far M (x ++ pickWitness A x m) t _ (by omega) (by omega)
      have hstep : tabRow M (x ++ pickWitness A x m) (t + 1) (x.length + m + T + 2) =
          M.rule (tabRow M (x ++ pickWitness A x m) t (x.length + m + T + 1))
            (tabRow M (x ++ pickWitness A x m) t (x.length + m + T + 2))
            (tabRow M (x ++ pickWitness A x m) t (x.length + m + T + 3)) :=
        tabRow_step_interior M (x ++ pickWitness A x m) t (x.length + m + T + 1)
      rw [hlast, hp, ih _ (by omega), ih _ (by omega), hW1, hW2, hstep, hfar]
      rfl
    · -- interior column
      have hi0 : i0 < tabWidth T x m - 2 := by omega
      have ha := pick_spec A T (tabWidth T x m) t i0 hcell (by omega) (by omega)
      have hb := pick_spec A T (tabWidth T x m) t (i0 + 1) hcell (by omega) (by omega)
      have hd := pick_spec A T (tabWidth T x m) t (i0 + 2) hcell (by omega) (by omega)
      have hcl := (CNF.eval_eq_true_iff _ _).mp htrans _
        (List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (by omega),
          List.mem_append_left _ (List.mem_append_right _
            (List.mem_flatMap.mpr ⟨i0, List.mem_range.mpr hi0,
              List.mem_flatMap.mpr ⟨pick A t i0, mem_cellList _,
                List.mem_flatMap.mpr ⟨pick A t (i0 + 1), mem_cellList _,
                  List.mem_map_of_mem (mem_cellList (pick A t (i0 + 2)))⟩⟩⟩))⟩)
      have hres : A (t + 1, i0 + 1,
          M.rule (pick A t i0) (pick A t (i0 + 1)) (pick A t (i0 + 2))) = true := by
        simpa [Clause.eval, Lit.eval, ha, hb, hd] using hcl
      have hp := (pick_uniq A T (tabWidth T x m) (t + 1) (i0 + 1) hcell ht (by omega) _ hres).symm
      rw [hp, ih i0 (by omega), ih (i0 + 1) (by omega), ih (i0 + 2) (by omega),
        tabRow_step_interior]

theorem pick_eq_tabRow {n : Nat} (M : TM n) (T : Nat) (x : List Bool) (m : Nat)
    (A : TVar n → Bool)
    (hcell : CNF.eval A (cellClauses n T (tabWidth T x m)) = true)
    (hinit : CNF.eval A (initClauses M T x m) = true)
    (htrans : CNF.eval A (transClauses M T (tabWidth T x m)) = true) :
    ∀ t, t ≤ T → ∀ i, i < tabWidth T x m →
      pick A t i = tabRow M (x ++ pickWitness A x m) t i := by
  intro t
  induction t with
  | zero => intro _; exact pick_eq_tabRow_zero M T x m A hcell hinit
  | succ t ih =>
    intro ht
    exact pick_eq_tabRow_step M T x m A hcell htrans t ht (ih (by omega))

theorem accepts_of_satisfiable_tableau {n : Nat} (M : TM n) (T : Nat) (x : List Bool) (m : Nat)
    (h : Satisfiable (tableau M T x m)) :
    ∃ w : List Bool, w.length = m ∧ M.Accepts T (x ++ w) := by
  obtain ⟨A, hA⟩ := h
  rw [tableau, CNF.eval_append, CNF.eval_append, CNF.eval_append] at hA
  obtain ⟨⟨⟨hcell, hinit⟩, htrans⟩, hacc⟩ := hA
  refine ⟨pickWitness A x m, pickWitness_length A x m, ?_⟩
  have hrow := pick_eq_tabRow M T x m A hcell hinit htrans
  have hcl := (CNF.eval_eq_true_iff _ _).mp hacc _ (List.mem_singleton.mpr rfl)
  rw [Clause.eval_eq_true_iff] at hcl
  obtain ⟨l, hl, hlv⟩ := hcl
  simp only [acceptClause, List.mem_flatMap, List.mem_range, List.mem_map] at hl
  obtain ⟨t, ht, i, hi, γ, -, rfl⟩ := hl
  have hAv : A (t, i, (γ, some M.accept)) = true := by simpa [Lit.eval] using hlv
  have hpick := pick_uniq A T (tabWidth T x m) t i hcell (by omega) hi _ hAv
  have hcellEq : ((γ : Sym), some M.accept) = tabRow M (x ++ pickWitness A x m) t i :=
    hpick.trans (hrow t (by omega) i hi)
  refine ⟨t, by omega, ?_⟩
  have h2 : (if (M.run t (M.initCfg (x ++ pickWitness A x m))).head = i then
      some (M.run t (M.initCfg (x ++ pickWitness A x m))).state else none) = some M.accept := by
    have h3 := congrArg Prod.snd hcellEq
    simpa [tabRow, Cfg.cell] using h3.symm
  by_cases hh : (M.run t (M.initCfg (x ++ pickWitness A x m))).head = i
  · rw [if_pos hh] at h2
    exact Option.some.inj h2
  · rw [if_neg hh] at h2
    exact absurd h2 (by simp)

/-- Correctness of the tableau reduction. -/
theorem satisfiable_tableau_iff {n : Nat} (M : TM n) (T : Nat) (x : List Bool) (m : Nat) :
    Satisfiable (tableau M T x m) ↔ ∃ w : List Bool, w.length = m ∧ M.Accepts T (x ++ w) := by
  constructor
  · exact accepts_of_satisfiable_tableau M T x m
  · rintro ⟨w, hw, hacc⟩
    exact satisfiable_tableau_of_accepts M T x m w hw hacc

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

