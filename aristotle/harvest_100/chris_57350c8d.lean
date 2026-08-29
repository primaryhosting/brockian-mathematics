/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses no `import`, so that the module
docstring above can literally be the first thing in the file).  The definitions of `Lit`,
`Clause`, `CNF`, `Clause.eval` and `CNF.eval` below mirror `Std.Sat.Literal`,
`Std.Sat.CNF.Clause`, `Std.Sat.CNF`, `Std.Sat.CNF.Clause.eval` and `Std.Sat.CNF.eval`
from the Lean standard library.
-/

namespace Frontier

/-! ## Propositional formulas in conjunctive normal form -/

/-- A literal: a variable together with the sign with which it occurs. -/
abbrev Lit (V : Type) := V × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause (V : Type) := List (Lit V)

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF (V : Type) := List (Clause V)

/-- Value of a clause under an assignment. -/
def Clause.eval {V : Type} (a : V → Bool) (c : Clause V) : Bool :=
  c.any fun l => a l.1 == l.2

/-- Value of a CNF formula under an assignment. -/
def CNF.eval {V : Type} (a : V → Bool) (f : CNF V) : Bool :=
  f.all fun c => Clause.eval a c

/-- `SAT`: a CNF formula is satisfiable if some assignment makes it true. -/
def Satisfiable {V : Type} (f : CNF V) : Prop :=
  ∃ a : V → Bool, CNF.eval a f = true

theorem cnf_eval_iff {V : Type} (a : V → Bool) (f : CNF V) :
    CNF.eval a f = true ↔ ∀ c ∈ f, Clause.eval a c = true := by
  simp [CNF.eval, List.all_eq_true]

theorem clause_eval_iff {V : Type} (a : V → Bool) (c : Clause V) :
    Clause.eval a c = true ↔ ∃ l ∈ c, a l.1 = l.2 := by
  simp [Clause.eval, List.any_eq_true]

/-- A positive literal. -/
def lp {V : Type} (v : V) : Lit V := (v, true)

/-- A negative literal. -/
def ln {V : Type} (v : V) : Lit V := (v, false)

/-! ## Nondeterministic Turing machines -/

/-- Tape symbols: `none` is the blank symbol. -/
abbrev Sym := Option Bool

/-- Head movements. -/
inductive Move where
  | left : Move
  | right : Move
  | stay : Move
  deriving DecidableEq

/-- Effect of a head movement on a position (the tape is one-way infinite, so moving
left at position `0` stays at `0`). -/
def Move.apply : Move → Nat → Nat
  | .left, i => i - 1
  | .right, i => i + 1
  | .stay, i => i

theorem Move.apply_le (d : Move) (i : Nat) : d.apply i ≤ i + 1 := by
  cases d <;> simp [Move.apply] <;> omega

/-- A nondeterministic Turing machine with tape alphabet `Sym = Option Bool` and
state set `{0, ..., numStates - 1}`.  `step q a` lists the possible successor triples
(new state, symbol written, head movement). -/
structure NTM where
  numStates : Nat
  start : Nat
  accept : Nat
  step : Nat → Sym → List (Nat × Sym × Move)
  start_lt : start < numStates
  accept_lt : accept < numStates
  step_lt : ∀ q a p, p ∈ step q a → p.1 < numStates
  step_ne : ∀ q a, step q a ≠ []

/-- A configuration: current state, tape contents, head position. -/
structure Cfg where
  state : Nat
  tape : Nat → Sym
  head : Nat

/-- Update a tape at one position. -/
def writeTape (f : Nat → Sym) (i : Nat) (s : Sym) : Nat → Sym :=
  fun j => if j = i then s else f j

/-- One step of the machine. -/
def NTM.Step (M : NTM) (c c' : Cfg) : Prop :=
  ∃ p ∈ M.step c.state (c.tape c.head),
    c'.state = p.1 ∧ c'.tape = writeTape c.tape c.head p.2.1 ∧ c'.head = p.2.2.apply c.head

/-- The tape holding the input, padded with blanks. -/
def inputTape (x : List Bool) : Nat → Sym := fun i => x[i]?

/-- The initial configuration on input `x`. -/
def NTM.init (M : NTM) (x : List Bool) : Cfg := ⟨M.start, inputTape x, 0⟩

/-- `c` is a computation of `M` on input `x` of length `T`. -/
def NTM.Run (M : NTM) (x : List Bool) (T : Nat) (c : Nat → Cfg) : Prop :=
  c 0 = M.init x ∧ ∀ t, t < T → M.Step (c t) (c (t + 1))

/-- `M` accepts `x` within `T` steps. -/
def NTM.AcceptsWithin (M : NTM) (x : List Bool) (T : Nat) : Prop :=
  ∃ c, M.Run x T c ∧ ∃ t, t ≤ T ∧ (c t).state = M.accept

/-- A language of bit strings is in `NP` if it is decided by a nondeterministic Turing
machine whose running time is bounded by a polynomial in the length of the input. -/
def InNP (L : List Bool → Prop) : Prop :=
  ∃ (M : NTM) (b k : Nat), ∀ x, L x ↔ M.AcceptsWithin x (b * (x.length + 1) ^ k)

/-! ## The variables of the tableau formula -/

/-- Propositional variables are (tagged) tuples of natural numbers; in particular the
variable type is countable. -/
abbrev Var := Nat × Nat × Nat × Nat × Nat × Nat × Nat

def symCode : Sym → Nat
  | none => 0
  | some false => 1
  | some true => 2

def moveCode : Move → Nat
  | .left => 0
  | .right => 1
  | .stay => 2

theorem symCode_inj {s s' : Sym} (h : symCode s = symCode s') : s = s' := by
  cases s with
  | none => cases s' with
    | none => rfl
    | some b => cases b <;> simp [symCode] at h
  | some b => cases b <;> cases s' with
    | none => simp [symCode] at h
    | some b' => cases b' <;> simp_all [symCode]

theorem moveCode_inj {d d' : Move} (h : moveCode d = moveCode d') : d = d' := by
  cases d <;> cases d' <;> simp_all [moveCode]

/-- `vS t q` : at time `t` the machine is in state `q`. -/
def vS (t q : Nat) : Var := (0, t, q, 0, 0, 0, 0)

/-- `vH t i` : at time `t` the head is at position `i`. -/
def vH (t i : Nat) : Var := (1, t, i, 0, 0, 0, 0)

/-- `vC t i s` : at time `t` the tape cell `i` carries the symbol `s`. -/
def vC (t i : Nat) (s : Sym) : Var := (2, t, i, symCode s, 0, 0, 0)

/-- A transition tuple `(q, a, q', b, d)`. -/
abbrev Trans := Nat × Sym × Nat × Sym × Move

/-- `vTr t τ` : the step from time `t` to time `t+1` uses the transition `τ`. -/
def vTr (t : Nat) (τ : Trans) : Var :=
  (3, t, τ.1, symCode τ.2.1, τ.2.2.1, symCode τ.2.2.2.1, moveCode τ.2.2.2.2)

/-- The three tape symbols. -/
def syms : List Sym := [none, some false, some true]

theorem mem_syms (s : Sym) : s ∈ syms := by
  cases s with
  | none => simp [syms]
  | some b => cases b <;> simp [syms]

/-- All transitions of `M`, as an explicit list. -/
def transList (M : NTM) : List Trans :=
  (List.range M.numStates).flatMap fun q =>
    syms.flatMap fun a => (M.step q a).map fun p => (q, a, p.1, p.2.1, p.2.2)

theorem mem_transList {M : NTM} {τ : Trans} :
    τ ∈ transList M ↔ τ.1 < M.numStates ∧ (τ.2.2.1, τ.2.2.2.1, τ.2.2.2.2) ∈ M.step τ.1 τ.2.1 := by
  obtain ⟨q, a, q', b, d⟩ := τ
  constructor
  · intro h
    simp only [transList, List.mem_flatMap, List.mem_map, List.mem_range] at h
    obtain ⟨q0, hq0, a0, _, p, hp, hpe⟩ := h
    simp only [Prod.mk.injEq] at hpe
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpe
    subst h1; subst h2; subst h3; subst h4; subst h5
    exact ⟨hq0, hp⟩
  · rintro ⟨h1, h2⟩
    simp only [transList, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨q, h1, a, mem_syms a, (q', b, d), h2, rfl⟩

/-! ## The tableau formula -/

section Tableau

variable (M : NTM) (T : Nat) (x : List Bool)

/-- At each time the machine is in at least one state. -/
def stateOne : CNF Var :=
  (List.range (T + 1)).map fun t => (List.range M.numStates).map fun q => lp (vS t q)

/-- At each time the machine is in at most one state. -/
def stateAtMostOne : CNF Var :=
  (List.range (T + 1)).flatMap fun t =>
    (List.range M.numStates).flatMap fun q =>
      (List.range M.numStates).flatMap fun q' =>
        if q = q' then ([] : CNF Var) else [[ln (vS t q), ln (vS t q')]]

/-- At time `t` the head is at one of the positions `0, ..., t`. -/
def headOne : CNF Var :=
  (List.range (T + 1)).map fun t => (List.range (t + 1)).map fun i => lp (vH t i)

/-- The head is at at most one position. -/
def headAtMostOne : CNF Var :=
  (List.range (T + 1)).flatMap fun t =>
    (List.range (T + 1)).flatMap fun i =>
      (List.range (T + 1)).flatMap fun j =>
        if i = j then ([] : CNF Var) else [[ln (vH t i), ln (vH t j)]]

/-- Every cell carries at least one symbol. -/
def cellOne : CNF Var :=
  (List.range (T + 1)).flatMap fun t =>
    (List.range (T + 1)).map fun i => syms.map fun s => lp (vC t i s)

/-- Every cell carries at most one symbol. -/
def cellAtMostOne : CNF Var :=
  (List.range (T + 1)).flatMap fun t =>
    (List.range (T + 1)).flatMap fun i =>
      syms.flatMap fun s =>
        syms.flatMap fun s' =>
          if s = s' then ([] : CNF Var) else [[ln (vC t i s), ln (vC t i s')]]

/-- The computation starts in the initial configuration on input `x`. -/
def initClauses : CNF Var :=
  [lp (vS 0 M.start)] :: [lp (vH 0 0)] ::
    (List.range (T + 1)).map fun i => [lp (vC 0 i (inputTape x i))]

/-- At some time the machine is in the accepting state. -/
def acceptClause : CNF Var :=
  [(List.range (T + 1)).map fun t => lp (vS t M.accept)]

/-- At each time step at least one transition is taken. -/
def transOne : CNF Var :=
  (List.range T).map fun t => (transList M).map fun τ => lp (vTr t τ)

/-- The consequences of taking a transition. -/
def transImp : CNF Var :=
  (List.range T).flatMap fun t =>
    (transList M).flatMap fun τ =>
      [[ln (vTr t τ), lp (vS t τ.1)], [ln (vTr t τ), lp (vS (t + 1) τ.2.2.1)]] ++
        (List.range (T + 1)).flatMap fun i =>
          [[ln (vTr t τ), ln (vH t i), lp (vC t i τ.2.1)],
            [ln (vTr t τ), ln (vH t i), lp (vC (t + 1) i τ.2.2.2.1)],
            [ln (vTr t τ), ln (vH t i), lp (vH (t + 1) (τ.2.2.2.2.apply i))]]

/-- Cells away from the head do not change. -/
def frameClauses : CNF Var :=
  (List.range T).flatMap fun t =>
    (List.range (T + 1)).flatMap fun j =>
      syms.map fun s => [lp (vH t j), ln (vC t j s), lp (vC (t + 1) j s)]

/-- The Cook–Levin tableau formula: a CNF formula which is satisfiable exactly when `M`
accepts `x` within `T` steps. -/
def tableau : CNF Var :=
  stateOne M T ++ stateAtMostOne M T ++ headOne T ++ headAtMostOne T ++ cellOne T ++
    cellAtMostOne T ++ initClauses M T x ++ acceptClause M T ++ transOne M T ++
    transImp M T ++ frameClauses T

end Tableau

/-! ## Membership of the individual clause families in the tableau -/

section Members

variable {M : NTM} {T : Nat} {x : List Bool} {c : Clause Var}

theorem mem_tab_stateOne (h : c ∈ stateOne M T) : c ∈ tableau M T x := by
  simp only [tableau, List.mem_append]; simp [h]

theorem mem_tab_stateAtMostOne (h : c ∈ stateAtMostOne M T) : c ∈ tableau M T x := by
  simp only [tableau, List.mem_append]; simp [h]

theorem mem_tab_headOne (h : c ∈ headOne T) : c ∈ tableau M T x := by
  simp only [tableau, List.mem_append]; simp [h]

theorem mem_tab_headAtMostOne (h : c ∈ headAtMostOne T) : c ∈ tableau M T x := by
  simp only [tableau, List.mem_append]; simp [h]

theorem mem_tab_cellOne (h : c ∈ cellOne T) : c ∈ tableau M T x := by
  simp only [tableau, List.mem_append]; simp [h]

theorem mem_tab_cellAtMostOne (h : c ∈ cellAtMostOne T) : c ∈ tableau M T x := by
  simp only [tableau, List.mem_append]; simp [h]

theorem mem_tab_initClauses (h : c ∈ initClauses M T x) : c ∈ tableau M T x := by
  simp only [tableau, List.mem_append]; simp [h]

theorem mem_tab_acceptClause (h : c ∈ acceptClause M T) : c ∈ tableau M T x := by
  simp only [tableau, List.mem_append]; simp [h]

theorem mem_tab_transOne (h : c ∈ transOne M T) : c ∈ tableau M T x := by
  simp only [tableau, List.mem_append]; simp [h]

theorem mem_tab_transImp (h : c ∈ transImp M T) : c ∈ tableau M T x := by
  simp only [tableau, List.mem_append]; simp [h]

theorem mem_tab_frameClauses (h : c ∈ frameClauses T) : c ∈ tableau M T x := by
  simp only [tableau, List.mem_append]; simp [h]

end Members

/-! ## Decoding an assignment -/

/-- `pick p n` is a witness `q < n` with `p q = true`, if there is one. -/
def pick (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if p n then n else pick p n

theorem pick_spec {p : Nat → Bool} : ∀ {n : Nat}, (∃ q, q < n ∧ p q = true) →
    pick p n < n ∧ p (pick p n) = true := by
  intro n
  induction n with
  | zero => intro h; obtain ⟨q, hq, -⟩ := h; omega
  | succ n ih =>
    intro h
    by_cases hp : p n = true
    · refine ⟨?_, ?_⟩ <;> simp [pick, hp]
    · obtain ⟨q, hq, hpq⟩ := h
      have hq' : q < n := by
        have : q < n ∨ q = n := by omega
        rcases this with h' | h'
        · exact h'
        · exact absurd (h' ▸ hpq) hp
      have hrec := ih ⟨q, hq', hpq⟩
      have hpk : pick p (n + 1) = pick p n := by simp [pick, hp]
      rw [hpk]
      exact ⟨by omega, hrec.2⟩

/-- The state read off an assignment. -/
def stateOf (A : Var → Bool) (n t : Nat) : Nat := pick (fun q => A (vS t q)) n

/-- The head position read off an assignment. -/
def headOf (A : Var → Bool) (T t : Nat) : Nat := pick (fun i => A (vH t i)) (T + 1)

/-- The tape read off an assignment. -/
def tapeOf (A : Var → Bool) (T : Nat) (x : List Bool) (t j : Nat) : Sym :=
  if j ≤ T then
    (if A (vC t j none) then none
      else if A (vC t j (some false)) then some false else some true)
  else inputTape x j

/-- The configuration at time `t` read off an assignment. -/
def cfgOf (M : NTM) (A : Var → Bool) (T : Nat) (x : List Bool) (t : Nat) : Cfg :=
  ⟨stateOf A M.numStates t, tapeOf A T x t, headOf A T t⟩

/-! ## Reading facts off a satisfying assignment -/

section Extract

variable {M : NTM} {T : Nat} {x : List Bool} {A : Var → Bool}
  (hsat : ∀ c ∈ tableau M T x, Clause.eval A c = true)

include hsat

theorem ex_state {t : Nat} (ht : t ≤ T) : ∃ q, q < M.numStates ∧ A (vS t q) = true := by
  have hc : ((List.range M.numStates).map fun q => lp (vS t q)) ∈ stateOne M T := by
    simp only [stateOne, List.mem_map, List.mem_range]
    exact ⟨t, by omega, rfl⟩
  have h := hsat _ (mem_tab_stateOne hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_map, List.mem_range] at hl
  obtain ⟨q, hq, rfl⟩ := hl
  exact ⟨q, hq, by simpa [lp] using hv⟩

theorem uniq_state {t q q' : Nat} (ht : t ≤ T) (hq : q < M.numStates) (hq' : q' < M.numStates)
    (h1 : A (vS t q) = true) (h2 : A (vS t q') = true) : q = q' := by
  by_cases hne : q = q'
  · exact hne
  exfalso
  have hc : [ln (vS t q), ln (vS t q')] ∈ stateAtMostOne M T := by
    simp only [stateAtMostOne, List.mem_flatMap, List.mem_range]
    exact ⟨t, by omega, q, hq, q', hq', by simp [hne]⟩
  have h := hsat _ (mem_tab_stateAtMostOne hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · simp [ln, h1] at hv
  · simp [ln, h2] at hv

theorem ex_head {t : Nat} (ht : t ≤ T) : ∃ i, i ≤ t ∧ A (vH t i) = true := by
  have hc : ((List.range (t + 1)).map fun i => lp (vH t i)) ∈ headOne T := by
    simp only [headOne, List.mem_map, List.mem_range]
    exact ⟨t, by omega, rfl⟩
  have h := hsat _ (mem_tab_headOne hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_map, List.mem_range] at hl
  obtain ⟨i, hi, rfl⟩ := hl
  exact ⟨i, by omega, by simpa [lp] using hv⟩

theorem uniq_head {t i j : Nat} (ht : t ≤ T) (hi : i ≤ T) (hj : j ≤ T)
    (h1 : A (vH t i) = true) (h2 : A (vH t j) = true) : i = j := by
  by_cases hne : i = j
  · exact hne
  exfalso
  have hc : [ln (vH t i), ln (vH t j)] ∈ headAtMostOne T := by
    simp only [headAtMostOne, List.mem_flatMap, List.mem_range]
    exact ⟨t, by omega, i, by omega, j, by omega, by simp [hne]⟩
  have h := hsat _ (mem_tab_headAtMostOne hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · simp [ln, h1] at hv
  · simp [ln, h2] at hv

theorem ex_cell {t i : Nat} (ht : t ≤ T) (hi : i ≤ T) : ∃ s, A (vC t i s) = true := by
  have hc : (syms.map fun s => lp (vC t i s)) ∈ cellOne T := by
    simp only [cellOne, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨t, by omega, i, by omega, rfl⟩
  have h := hsat _ (mem_tab_cellOne hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_map] at hl
  obtain ⟨s, _, rfl⟩ := hl
  exact ⟨s, by simpa [lp] using hv⟩

theorem uniq_cell {t i : Nat} {s s' : Sym} (ht : t ≤ T) (hi : i ≤ T)
    (h1 : A (vC t i s) = true) (h2 : A (vC t i s') = true) : s = s' := by
  by_cases hne : s = s'
  · exact hne
  exfalso
  have hc : [ln (vC t i s), ln (vC t i s')] ∈ cellAtMostOne T := by
    simp only [cellAtMostOne, List.mem_flatMap, List.mem_range]
    exact ⟨t, by omega, i, by omega, s, mem_syms s, s', mem_syms s', by simp [hne]⟩
  have h := hsat _ (mem_tab_cellAtMostOne hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · simp [ln, h1] at hv
  · simp [ln, h2] at hv

theorem init_state : A (vS 0 M.start) = true := by
  have hc : [lp (vS 0 M.start)] ∈ initClauses M T x := by simp [initClauses]
  have h := hsat _ (mem_tab_initClauses hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  subst hl; simpa [lp] using hv

theorem init_head : A (vH 0 0) = true := by
  have hc : [lp (vH 0 0)] ∈ initClauses M T x := by simp [initClauses]
  have h := hsat _ (mem_tab_initClauses hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  subst hl; simpa [lp] using hv

theorem init_cell {i : Nat} (hi : i ≤ T) : A (vC 0 i (inputTape x i)) = true := by
  have hc : [lp (vC 0 i (inputTape x i))] ∈ initClauses M T x := by
    simp only [initClauses, List.mem_cons, List.mem_map, List.mem_range]
    exact Or.inr (Or.inr ⟨i, by omega, rfl⟩)
  have h := hsat _ (mem_tab_initClauses hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  subst hl; simpa [lp] using hv

theorem ex_accept : ∃ t, t ≤ T ∧ A (vS t M.accept) = true := by
  have hc : ((List.range (T + 1)).map fun t => lp (vS t M.accept)) ∈ acceptClause M T := by
    simp [acceptClause]
  have h := hsat _ (mem_tab_acceptClause hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_map, List.mem_range] at hl
  obtain ⟨t, ht, rfl⟩ := hl
  exact ⟨t, by omega, by simpa [lp] using hv⟩

theorem ex_trans {t : Nat} (ht : t < T) :
    ∃ τ, τ ∈ transList M ∧ A (vTr t τ) = true := by
  have hc : ((transList M).map fun τ => lp (vTr t τ)) ∈ transOne M T := by
    simp only [transOne, List.mem_map, List.mem_range]
    exact ⟨t, ht, rfl⟩
  have h := hsat _ (mem_tab_transOne hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_map] at hl
  obtain ⟨τ, hτ, rfl⟩ := hl
  exact ⟨τ, hτ, by simpa [lp] using hv⟩

theorem imp_state {t : Nat} {τ : Trans} (ht : t < T) (hτ : τ ∈ transList M)
    (h1 : A (vTr t τ) = true) : A (vS t τ.1) = true := by
  have hc : [ln (vTr t τ), lp (vS t τ.1)] ∈ transImp M T := by
    simp only [transImp, List.mem_flatMap, List.mem_range]
    exact ⟨t, ht, τ, hτ, List.mem_append_left _ (by simp)⟩
  have h := hsat _ (mem_tab_transImp hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · simp [ln, h1] at hv
  · simpa [lp] using hv

theorem imp_next_state {t : Nat} {τ : Trans} (ht : t < T) (hτ : τ ∈ transList M)
    (h1 : A (vTr t τ) = true) : A (vS (t + 1) τ.2.2.1) = true := by
  have hc : [ln (vTr t τ), lp (vS (t + 1) τ.2.2.1)] ∈ transImp M T := by
    simp only [transImp, List.mem_flatMap, List.mem_range]
    exact ⟨t, ht, τ, hτ, List.mem_append_left _ (by simp)⟩
  have h := hsat _ (mem_tab_transImp hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · simp [ln, h1] at hv
  · simpa [lp] using hv

theorem imp_read {t i : Nat} {τ : Trans} (ht : t < T) (hτ : τ ∈ transList M) (hi : i ≤ T)
    (h1 : A (vTr t τ) = true) (h2 : A (vH t i) = true) : A (vC t i τ.2.1) = true := by
  have hc : [ln (vTr t τ), ln (vH t i), lp (vC t i τ.2.1)] ∈ transImp M T := by
    simp only [transImp, List.mem_flatMap, List.mem_range]
    refine ⟨t, ht, τ, hτ, List.mem_append_right _ ?_⟩
    simp only [List.mem_flatMap, List.mem_range]
    exact ⟨i, by omega, by simp⟩
  have h := hsat _ (mem_tab_transImp hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · simp [ln, h1] at hv
  · simp [ln, h2] at hv
  · simpa [lp] using hv

theorem imp_write {t i : Nat} {τ : Trans} (ht : t < T) (hτ : τ ∈ transList M) (hi : i ≤ T)
    (h1 : A (vTr t τ) = true) (h2 : A (vH t i) = true) :
    A (vC (t + 1) i τ.2.2.2.1) = true := by
  have hc : [ln (vTr t τ), ln (vH t i), lp (vC (t + 1) i τ.2.2.2.1)] ∈ transImp M T := by
    simp only [transImp, List.mem_flatMap, List.mem_range]
    refine ⟨t, ht, τ, hτ, List.mem_append_right _ ?_⟩
    simp only [List.mem_flatMap, List.mem_range]
    exact ⟨i, by omega, by simp⟩
  have h := hsat _ (mem_tab_transImp hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · simp [ln, h1] at hv
  · simp [ln, h2] at hv
  · simpa [lp] using hv

theorem imp_move {t i : Nat} {τ : Trans} (ht : t < T) (hτ : τ ∈ transList M) (hi : i ≤ T)
    (h1 : A (vTr t τ) = true) (h2 : A (vH t i) = true) :
    A (vH (t + 1) (τ.2.2.2.2.apply i)) = true := by
  have hc : [ln (vTr t τ), ln (vH t i), lp (vH (t + 1) (τ.2.2.2.2.apply i))] ∈ transImp M T := by
    simp only [transImp, List.mem_flatMap, List.mem_range]
    refine ⟨t, ht, τ, hτ, List.mem_append_right _ ?_⟩
    simp only [List.mem_flatMap, List.mem_range]
    exact ⟨i, by omega, by simp⟩
  have h := hsat _ (mem_tab_transImp hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · simp [ln, h1] at hv
  · simp [ln, h2] at hv
  · simpa [lp] using hv

theorem frame_step {t j : Nat} {s : Sym} (ht : t < T) (hj : j ≤ T)
    (h1 : A (vH t j) = false) (h2 : A (vC t j s) = true) : A (vC (t + 1) j s) = true := by
  have hc : [lp (vH t j), ln (vC t j s), lp (vC (t + 1) j s)] ∈ frameClauses T := by
    simp only [frameClauses, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨t, ht, j, by omega, s, mem_syms s, rfl⟩
  have h := hsat _ (mem_tab_frameClauses hc)
  rw [clause_eval_iff] at h
  obtain ⟨l, hl, hv⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · simp [lp, h1] at hv
  · simp [ln, h2] at hv
  · simpa [lp] using hv

/-! ## Extracting a computation from a satisfying assignment -/

omit hsat in
@[simp] theorem cfgOf_state (t : Nat) : (cfgOf M A T x t).state = stateOf A M.numStates t := rfl

omit hsat in
@[simp] theorem cfgOf_tape (t : Nat) : (cfgOf M A T x t).tape = tapeOf A T x t := rfl

omit hsat in
@[simp] theorem cfgOf_head (t : Nat) : (cfgOf M A T x t).head = headOf A T t := rfl

theorem stateOf_spec {t : Nat} (ht : t ≤ T) :
    stateOf A M.numStates t < M.numStates ∧ A (vS t (stateOf A M.numStates t)) = true :=
  pick_spec (ex_state hsat ht)

theorem headOf_spec {t : Nat} (ht : t ≤ T) :
    headOf A T t ≤ T ∧ A (vH t (headOf A T t)) = true := by
  obtain ⟨i, hi, hiA⟩ := ex_head hsat ht
  have h := pick_spec (p := fun i => A (vH t i)) (n := T + 1) ⟨i, by omega, hiA⟩
  refine ⟨?_, h.2⟩
  have he : headOf A T t = pick (fun i => A (vH t i)) (T + 1) := rfl
  have := h.1
  omega

theorem headOf_le {t : Nat} (ht : t ≤ T) : headOf A T t ≤ t := by
  obtain ⟨i, hi, hiA⟩ := ex_head hsat ht
  have h2 := headOf_spec hsat ht
  have := uniq_head hsat ht h2.1 (by omega : i ≤ T) h2.2 hiA
  omega

theorem tapeOf_spec {t j : Nat} (ht : t ≤ T) (hj : j ≤ T) :
    A (vC t j (tapeOf A T x t j)) = true := by
  obtain ⟨s, hs⟩ := ex_cell hsat ht hj
  unfold tapeOf
  rw [if_pos hj]
  by_cases h0 : A (vC t j none) = true
  · simp [h0]
  · by_cases h1 : A (vC t j (some false)) = true
    · simp [h0, h1]
    · simp only [h0, h1, if_false, Bool.false_eq_true]
      cases s with
      | none => exact absurd hs h0
      | some bb =>
        cases bb with
        | false => exact absurd hs h1
        | true => exact hs

omit hsat in
theorem tapeOf_out {t j : Nat} (hj : ¬ j ≤ T) : tapeOf A T x t j = inputTape x j := by
  simp [tapeOf, hj]

theorem cfgOf_zero : cfgOf M A T x 0 = M.init x := by
  have h0 : (0 : Nat) ≤ T := Nat.zero_le _
  have hs := stateOf_spec hsat h0
  have hh := headOf_spec hsat h0
  have e1 : stateOf A M.numStates 0 = M.start :=
    uniq_state hsat h0 hs.1 M.start_lt hs.2 (init_state hsat)
  have e2 : headOf A T 0 = 0 :=
    uniq_head hsat h0 hh.1 h0 hh.2 (init_head hsat)
  have e3 : tapeOf A T x 0 = inputTape x := by
    funext j
    by_cases hj : j ≤ T
    · exact uniq_cell hsat h0 hj (tapeOf_spec hsat h0 hj) (init_cell hsat hj)
    · exact tapeOf_out hj
  simp [cfgOf, NTM.init, e1, e2, e3]

theorem step_of_sat {t : Nat} (ht : t < T) :
    M.Step (cfgOf M A T x t) (cfgOf M A T x (t + 1)) := by
  have ht' : t ≤ T := by omega
  have ht1 : t + 1 ≤ T := by omega
  obtain ⟨τ, hτ, hτA⟩ := ex_trans hsat ht
  obtain ⟨q, a, q', b, d⟩ := τ
  have hmem := mem_transList.mp hτ
  simp only at hmem
  have hst := stateOf_spec hsat ht'
  have hst1 := stateOf_spec hsat ht1
  have hhd := headOf_spec hsat ht'
  have hhd1 := headOf_spec hsat ht1
  have hhdle := headOf_le hsat ht'
  have hq : q = stateOf A M.numStates t :=
    uniq_state hsat ht' hmem.1 hst.1 (imp_state hsat ht hτ hτA) hst.2
  have hrd : A (vC t (headOf A T t) a) = true := imp_read hsat ht hτ hhd.1 hτA hhd.2
  have ha : a = tapeOf A T x t (headOf A T t) :=
    uniq_cell hsat ht' hhd.1 hrd (tapeOf_spec hsat ht' hhd.1)
  have hq'lt : q' < M.numStates := M.step_lt q a (q', b, d) hmem.2
  have hq' : q' = stateOf A M.numStates (t + 1) :=
    uniq_state hsat ht1 hq'lt hst1.1 (imp_next_state hsat ht hτ hτA) hst1.2
  have hb : b = tapeOf A T x (t + 1) (headOf A T t) :=
    uniq_cell hsat ht1 hhd.1 (imp_write hsat ht hτ hhd.1 hτA hhd.2) (tapeOf_spec hsat ht1 hhd.1)
  have hdlt : d.apply (headOf A T t) ≤ T := by
    have := Move.apply_le d (headOf A T t); omega
  have hmv : d.apply (headOf A T t) = headOf A T (t + 1) :=
    uniq_head hsat ht1 hdlt hhd1.1 (imp_move hsat ht hτ hhd.1 hτA hhd.2) hhd1.2
  refine ⟨(q', b, d), ?_, ?_, ?_, ?_⟩
  · simp only [cfgOf_state, cfgOf_tape, cfgOf_head]
    rw [← hq, ← ha]
    exact hmem.2
  · simp only [cfgOf_state]; exact hq'.symm
  · simp only [cfgOf_tape, cfgOf_head]
    funext j
    by_cases hjh : j = headOf A T t
    · subst hjh
      simp only [writeTape, if_pos]
      exact hb.symm
    · simp only [writeTape, if_neg hjh]
      by_cases hj : j ≤ T
      · have hjf : A (vH t j) = false := by
          cases hjb : A (vH t j) with
          | false => rfl
          | true => exact absurd (uniq_head hsat ht' hj hhd.1 hjb hhd.2) hjh
        have h1 := frame_step hsat ht hj hjf (tapeOf_spec hsat ht' hj)
        exact (uniq_cell hsat ht1 hj (tapeOf_spec hsat ht1 hj) h1)
      · rw [tapeOf_out hj, tapeOf_out hj]
  · simp only [cfgOf_head]; exact hmv.symm

theorem accepts_of_sat_aux : M.AcceptsWithin x T := by
  refine ⟨cfgOf M A T x, ⟨cfgOf_zero hsat, fun t ht => step_of_sat hsat ht⟩, ?_⟩
  obtain ⟨t, ht, hacc⟩ := ex_accept hsat
  refine ⟨t, ht, ?_⟩
  have hs := stateOf_spec hsat ht
  simp only [cfgOf_state]
  exact uniq_state hsat ht hs.1 M.accept_lt hs.2 hacc

end Extract

theorem accepts_of_sat {M : NTM} {T : Nat} {x : List Bool} (h : Satisfiable (tableau M T x)) :
    M.AcceptsWithin x T := by
  obtain ⟨A, hA⟩ := h
  exact accepts_of_sat_aux ((cnf_eval_iff A _).mp hA)

/-! ## From an accepting computation to a satisfying assignment -/

/-- The data of the transition used at time `t` of the computation `c`. -/
def StepData (M : NTM) (c : Nat → Cfg) (t : Nat) (τ : Trans) : Prop :=
  τ.1 = (c t).state ∧ τ.2.1 = (c t).tape (c t).head ∧
    (τ.2.2.1, τ.2.2.2.1, τ.2.2.2.2) ∈ M.step τ.1 τ.2.1 ∧
    (c (t + 1)).state = τ.2.2.1 ∧
    (c (t + 1)).tape = writeTape (c t).tape (c t).head τ.2.2.2.1 ∧
    (c (t + 1)).head = τ.2.2.2.2.apply (c t).head

/-- The assignment describing the computation `c` with transitions `tr`. -/
def assignOf (c : Nat → Cfg) (tr : Nat → Trans) (v : Var) : Bool :=
  if v.1 = 0 then decide ((c v.2.1).state = v.2.2.1)
  else if v.1 = 1 then decide ((c v.2.1).head = v.2.2.1)
  else if v.1 = 2 then decide (symCode ((c v.2.1).tape v.2.2.1) = v.2.2.2.1)
  else if v.1 = 3 then
    decide ((tr v.2.1).1 = v.2.2.1 ∧ symCode (tr v.2.1).2.1 = v.2.2.2.1 ∧
      (tr v.2.1).2.2.1 = v.2.2.2.2.1 ∧ symCode (tr v.2.1).2.2.2.1 = v.2.2.2.2.2.1 ∧
      moveCode (tr v.2.1).2.2.2.2 = v.2.2.2.2.2.2)
  else false

section Complete

variable {M : NTM} {T : Nat} {x : List Bool} {c : Nat → Cfg} {tr : Nat → Trans}

@[simp] theorem assignOf_vS (t q : Nat) :
    assignOf c tr (vS t q) = decide ((c t).state = q) := rfl

@[simp] theorem assignOf_vH (t i : Nat) :
    assignOf c tr (vH t i) = decide ((c t).head = i) := rfl

@[simp] theorem assignOf_vC (t i : Nat) (s : Sym) :
    assignOf c tr (vC t i s) = decide (symCode ((c t).tape i) = symCode s) := rfl

theorem assignOf_vTr_iff (t : Nat) (τ : Trans) :
    assignOf c tr (vTr t τ) = true ↔ tr t = τ := by
  obtain ⟨q, a, q', b, d⟩ := τ
  have hval : assignOf c tr (vTr t (q, a, q', b, d)) =
      decide ((tr t).1 = q ∧ symCode (tr t).2.1 = symCode a ∧ (tr t).2.2.1 = q' ∧
        symCode (tr t).2.2.2.1 = symCode b ∧ moveCode (tr t).2.2.2.2 = moveCode d) := rfl
  rw [hval]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨q0, a0, q0', b0, d0⟩ := tr t
    simp only at h1 h2 h3 h4 h5
    rw [h1, symCode_inj h2, h3, symCode_inj h4, moveCode_inj h5]
  · intro h
    rw [h]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem run_state_lt (hrun : M.Run x T c) : ∀ t, t ≤ T → (c t).state < M.numStates := by
  intro t
  induction t with
  | zero => intro _; rw [hrun.1]; exact M.start_lt
  | succ t ih =>
    intro ht
    obtain ⟨p, hp, h1, -, -⟩ := hrun.2 t (by omega)
    rw [h1]
    exact M.step_lt _ _ p hp

theorem run_head_le (hrun : M.Run x T c) : ∀ t, t ≤ T → (c t).head ≤ t := by
  intro t
  induction t with
  | zero => intro _; rw [hrun.1]; simp [NTM.init]
  | succ t ih =>
    intro ht
    obtain ⟨p, -, -, -, h3⟩ := hrun.2 t (by omega)
    have h4 := Move.apply_le p.2.2 (c t).head
    have h5 := ih (by omega)
    rw [h3]
    omega

theorem sat_stateOne (hrun : M.Run x T c) :
    ∀ cl ∈ stateOne M T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [stateOne, List.mem_map, List.mem_range] at hcl
  obtain ⟨t, ht, rfl⟩ := hcl
  rw [clause_eval_iff]
  refine ⟨lp (vS t (c t).state), ?_, ?_⟩
  · simp only [List.mem_map, List.mem_range]
    exact ⟨(c t).state, run_state_lt hrun t (by omega), rfl⟩
  · simp [lp]

theorem sat_stateAtMostOne :
    ∀ cl ∈ stateAtMostOne M T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [stateAtMostOne, List.mem_flatMap, List.mem_range] at hcl
  obtain ⟨t, -, q, -, q', -, hcl⟩ := hcl
  by_cases hqq : q = q'
  · simp [hqq] at hcl
  · simp only [hqq, if_false, List.mem_cons, List.not_mem_nil, or_false] at hcl
    subst hcl
    rw [clause_eval_iff]
    by_cases hs : (c t).state = q
    · refine ⟨ln (vS t q'), by simp, ?_⟩
      simp only [ln, assignOf_vS, decide_eq_false_iff_not]
      omega
    · refine ⟨ln (vS t q), by simp, ?_⟩
      simp only [ln, assignOf_vS, decide_eq_false_iff_not]
      exact hs

theorem sat_headOne (hrun : M.Run x T c) :
    ∀ cl ∈ headOne T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [headOne, List.mem_map, List.mem_range] at hcl
  obtain ⟨t, ht, rfl⟩ := hcl
  rw [clause_eval_iff]
  refine ⟨lp (vH t (c t).head), ?_, ?_⟩
  · simp only [List.mem_map, List.mem_range]
    exact ⟨(c t).head, by have := run_head_le hrun t (by omega); omega, rfl⟩
  · simp [lp]

theorem sat_headAtMostOne :
    ∀ cl ∈ headAtMostOne T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [headAtMostOne, List.mem_flatMap, List.mem_range] at hcl
  obtain ⟨t, -, i, -, j, -, hcl⟩ := hcl
  by_cases hij : i = j
  · simp [hij] at hcl
  · simp only [hij, if_false, List.mem_cons, List.not_mem_nil, or_false] at hcl
    subst hcl
    rw [clause_eval_iff]
    by_cases hh : (c t).head = i
    · refine ⟨ln (vH t j), by simp, ?_⟩
      simp only [ln, assignOf_vH, decide_eq_false_iff_not]
      omega
    · refine ⟨ln (vH t i), by simp, ?_⟩
      simp only [ln, assignOf_vH, decide_eq_false_iff_not]
      exact hh

theorem sat_cellOne : ∀ cl ∈ cellOne T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [cellOne, List.mem_flatMap, List.mem_map, List.mem_range] at hcl
  obtain ⟨t, -, i, -, rfl⟩ := hcl
  rw [clause_eval_iff]
  refine ⟨lp (vC t i ((c t).tape i)), ?_, ?_⟩
  · simp only [List.mem_map]
    exact ⟨(c t).tape i, mem_syms _, rfl⟩
  · simp [lp]

theorem sat_cellAtMostOne : ∀ cl ∈ cellAtMostOne T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [cellAtMostOne, List.mem_flatMap, List.mem_range] at hcl
  obtain ⟨t, -, i, -, s, -, s', -, hcl⟩ := hcl
  by_cases hss : s = s'
  · simp [hss] at hcl
  · simp only [hss, if_false, List.mem_cons, List.not_mem_nil, or_false] at hcl
    subst hcl
    rw [clause_eval_iff]
    by_cases hc : (c t).tape i = s
    · refine ⟨ln (vC t i s'), by simp, ?_⟩
      simp only [ln, assignOf_vC, decide_eq_false_iff_not]
      intro hcon
      exact hss (hc ▸ symCode_inj hcon)
    · refine ⟨ln (vC t i s), by simp, ?_⟩
      simp only [ln, assignOf_vC, decide_eq_false_iff_not]
      intro hcon
      exact hc (symCode_inj hcon)

theorem sat_initClauses (hrun : M.Run x T c) :
    ∀ cl ∈ initClauses M T x, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  have h0 : c 0 = M.init x := hrun.1
  simp only [initClauses, List.mem_cons, List.mem_map, List.mem_range] at hcl
  rcases hcl with rfl | rfl | ⟨i, -, rfl⟩
  · rw [clause_eval_iff]
    exact ⟨lp (vS 0 M.start), by simp, by simp [lp, h0, NTM.init]⟩
  · rw [clause_eval_iff]
    exact ⟨lp (vH 0 0), by simp, by simp [lp, h0, NTM.init]⟩
  · rw [clause_eval_iff]
    exact ⟨lp (vC 0 i (inputTape x i)), by simp, by simp [lp, h0, NTM.init]⟩

theorem sat_acceptClause {t0 : Nat} (ht0 : t0 ≤ T) (hacc : (c t0).state = M.accept) :
    ∀ cl ∈ acceptClause M T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [acceptClause, List.mem_cons, List.not_mem_nil, or_false] at hcl
  subst hcl
  rw [clause_eval_iff]
  refine ⟨lp (vS t0 M.accept), ?_, ?_⟩
  · simp only [List.mem_map, List.mem_range]
    exact ⟨t0, by omega, rfl⟩
  · simp [lp, hacc]

theorem sat_transOne (hrun : M.Run x T c) (hd : ∀ t, t < T → StepData M c t (tr t)) :
    ∀ cl ∈ transOne M T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [transOne, List.mem_map, List.mem_range] at hcl
  obtain ⟨t, ht, rfl⟩ := hcl
  obtain ⟨e1, e2, e3, -, -, -⟩ := hd t ht
  rw [clause_eval_iff]
  refine ⟨lp (vTr t (tr t)), ?_, ?_⟩
  · simp only [List.mem_map]
    refine ⟨tr t, mem_transList.mpr ⟨?_, e3⟩, rfl⟩
    rw [e1]
    exact run_state_lt hrun t (by omega)
  · simp only [lp]
    exact (assignOf_vTr_iff t (tr t)).mpr rfl

theorem sat_transImp (hd : ∀ t, t < T → StepData M c t (tr t)) :
    ∀ cl ∈ transImp M T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [transImp, List.mem_flatMap, List.mem_range, List.mem_append] at hcl
  obtain ⟨t, ht, τ, hτ, hcl⟩ := hcl
  by_cases hA : assignOf c tr (vTr t τ) = true
  · have heq : tr t = τ := (assignOf_vTr_iff t τ).mp hA
    obtain ⟨e1, e2, -, e4, e5, e6⟩ := hd t ht
    rw [heq] at e1 e2 e4 e5 e6
    rcases hcl with hcl | hcl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · rw [clause_eval_iff]
        exact ⟨lp (vS t τ.1), by simp, by simp [lp, e1]⟩
      · rw [clause_eval_iff]
        exact ⟨lp (vS (t + 1) τ.2.2.1), by simp, by simp [lp, e4]⟩
    · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hcl
      obtain ⟨i, -, hcl⟩ := hcl
      by_cases hh : (c t).head = i
      · subst hh
        rcases hcl with rfl | rfl | rfl
        · rw [clause_eval_iff]
          exact ⟨lp (vC t (c t).head τ.2.1), by simp, by simp [lp, e2]⟩
        · rw [clause_eval_iff]
          refine ⟨lp (vC (t + 1) (c t).head τ.2.2.2.1), by simp, ?_⟩
          simp only [lp, assignOf_vC, decide_eq_true_eq, e5, writeTape, if_pos]
        · rw [clause_eval_iff]
          refine ⟨lp (vH (t + 1) (τ.2.2.2.2.apply (c t).head)), by simp, ?_⟩
          simp [lp, e6]
      · rcases hcl with rfl | rfl | rfl <;> rw [clause_eval_iff] <;>
          exact ⟨ln (vH t i), by simp, by simp [ln, hh]⟩
  · have hA' : assignOf c tr (vTr t τ) = false := by
      cases hv : assignOf c tr (vTr t τ) with
      | false => rfl
      | true => exact absurd hv hA
    rcases hcl with hcl | hcl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl <;> rw [clause_eval_iff] <;>
        exact ⟨ln (vTr t τ), by simp, by simp [ln, hA']⟩
    · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hcl
      obtain ⟨i, -, hcl⟩ := hcl
      rcases hcl with rfl | rfl | rfl <;> rw [clause_eval_iff] <;>
        exact ⟨ln (vTr t τ), by simp, by simp [ln, hA']⟩

theorem sat_frameClauses (hd : ∀ t, t < T → StepData M c t (tr t)) :
    ∀ cl ∈ frameClauses T, Clause.eval (assignOf c tr) cl = true := by
  intro cl hcl
  simp only [frameClauses, List.mem_flatMap, List.mem_map, List.mem_range] at hcl
  obtain ⟨t, ht, j, -, s, -, rfl⟩ := hcl
  rw [clause_eval_iff]
  by_cases hh : (c t).head = j
  · exact ⟨lp (vH t j), by simp, by simp [lp, hh]⟩
  · by_cases hs : (c t).tape j = s
    · obtain ⟨-, -, -, -, e5, -⟩ := hd t ht
      refine ⟨lp (vC (t + 1) j s), by simp, ?_⟩
      simp only [lp, assignOf_vC, decide_eq_true_eq, e5, writeTape, if_neg (fun h => hh h.symm)]
      rw [hs]
    · refine ⟨ln (vC t j s), by simp, ?_⟩
      simp only [ln, assignOf_vC, decide_eq_false_iff_not]
      intro hcon
      exact hs (symCode_inj hcon)

end Complete

theorem sat_of_accepts {M : NTM} {T : Nat} {x : List Bool} (h : M.AcceptsWithin x T) :
    Satisfiable (tableau M T x) := by
  obtain ⟨c, hrun, t0, ht0, hacc⟩ := h
  have hex : ∀ t : Nat, ∃ τ : Trans, t < T → StepData M c t τ := by
    intro t
    by_cases ht : t < T
    · obtain ⟨p, hp, h1, h2, h3⟩ := hrun.2 t ht
      exact ⟨((c t).state, (c t).tape (c t).head, p.1, p.2.1, p.2.2),
        fun _ => ⟨rfl, rfl, hp, h1, h2, h3⟩⟩
    · exact ⟨(0, none, 0, none, Move.stay), fun h' => absurd h' ht⟩
  obtain ⟨tr, htr⟩ := Classical.axiomOfChoice hex
  refine ⟨assignOf c tr, ?_⟩
  rw [cnf_eval_iff]
  intro cl hcl
  simp only [tableau, List.mem_append] at hcl
  rcases hcl with h | h | h | h | h | h | h | h | h | h | h
  · exact sat_stateOne hrun cl h
  · exact sat_stateAtMostOne cl h
  · exact sat_headOne hrun cl h
  · exact sat_headAtMostOne cl h
  · exact sat_cellOne cl h
  · exact sat_cellAtMostOne cl h
  · exact sat_initClauses hrun cl h
  · exact sat_acceptClause ht0 hacc cl h
  · exact sat_transOne hrun htr cl h
  · exact sat_transImp htr cl h
  · exact sat_frameClauses htr cl h

/-- **Correctness of the Cook–Levin tableau encoding**: the CNF formula `tableau M T x` is
satisfiable if and only if the nondeterministic machine `M` accepts the input `x` within
`T` steps. -/
theorem tableau_sat_iff (M : NTM) (T : Nat) (x : List Bool) :
    Satisfiable (tableau M T x) ↔ M.AcceptsWithin x T :=
  ⟨accepts_of_sat, sat_of_accepts⟩

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

