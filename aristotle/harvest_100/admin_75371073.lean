import Mathlib

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

/-!
## Overview

This file formalises the combinatorial core of the Cook–Levin theorem: *bounded
nondeterministic computation is reducible to Boolean satisfiability*.

The model of computation is a **sequential Boolean circuit machine**: a machine has a
configuration consisting of `width` bits, and one Boolean circuit (a straight-line
program of NAND gates, constants and reads of the current configuration) per output bit,
describing how the configuration is updated in one step.  Running the machine for `t`
steps from an initial configuration `c₀` and looking at the designated accepting bit
`acc` gives the acceptance predicate `Frontier.Accepts`.

Nondeterminism is the usual "guess" formulation: the input `x : List Bool` is written on
the first `x.length` bits of the initial configuration, and all remaining bits of the
initial configuration are unconstrained (they are the witness / nondeterministic guess).

The reduction `Frontier.tableau M x t` is the explicit computation tableau CNF:
a Boolean variable for every configuration bit at every time step, a Tseitin variable for
every gate of every step circuit at every time step, together with clauses forcing the
input bits, forcing the gate variables to compute the circuits, linking each layer to the
next, and asserting acceptance.

The main theorem `Frontier.cook_levin` says that `x` is accepted (for some witness) within
`t` steps **iff** the CNF `tableau M x t` is satisfiable, i.e. the explicit map
`x ↦ tableau M x (tb x.length)` is a many-one reduction of the language of `M` to `SAT`.
`Frontier.tableau_length_le` gives the accompanying size bound, which is polynomial
whenever the time bound, the width and the circuit sizes are polynomial; this is what
makes the reduction a polynomial-time (Karp) reduction.
-/

namespace Frontier

/-! ### CNF formulas -/

/-- An assignment of truth values to (natural-number indexed) Boolean variables. -/
abbrev Assign := ℕ → Bool

/-- A literal: a variable index together with the polarity that makes it true. -/
abbrev Lit := ℕ × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNFFormula := List Clause

/-- A clause is satisfied by `σ` when one of its literals is true under `σ`. -/
def clauseSat (σ : Assign) (c : Clause) : Prop := ∃ l ∈ c, σ l.1 = l.2

/-- A CNF formula is satisfiable when some assignment satisfies all of its clauses. -/
def Sat (φ : CNFFormula) : Prop := ∃ σ : Assign, ∀ c ∈ φ, clauseSat σ c

/-- The satisfiability language. -/
def SAT : Set CNFFormula := {φ | Sat φ}

lemma clauseSat_one {σ : Assign} {u : ℕ} {bu : Bool} :
    clauseSat σ [(u, bu)] ↔ σ u = bu := by
  simp [clauseSat]

lemma clauseSat_two {σ : Assign} {u v : ℕ} {bu bv : Bool} :
    clauseSat σ [(u, bu), (v, bv)] ↔ (σ u = bu ∨ σ v = bv) := by
  simp [clauseSat]

lemma clauseSat_three {σ : Assign} {u v w : ℕ} {bu bv bw : Bool} :
    clauseSat σ [(u, bu), (v, bv), (w, bw)] ↔ (σ u = bu ∨ σ v = bv ∨ σ w = bw) := by
  simp [clauseSat]

/-- Two clauses expressing `u ↔ v`, first half. -/
lemma clauseSat_eq₁ {σ : Assign} {u v : ℕ} (h : σ u = σ v) :
    clauseSat σ [(u, false), (v, true)] := by
  rw [clauseSat_two]
  cases hu : σ u
  · exact Or.inl rfl
  · exact Or.inr (h ▸ hu)

/-- Two clauses expressing `u ↔ v`, second half. -/
lemma clauseSat_eq₂ {σ : Assign} {u v : ℕ} (h : σ u = σ v) :
    clauseSat σ [(u, true), (v, false)] := by
  rw [clauseSat_two]
  cases hu : σ u
  · exact Or.inr (h ▸ hu)
  · exact Or.inl rfl

lemma clauseSat_nand₁ {σ : Assign} {p q o : ℕ} (h : σ o = !(σ p && σ q)) :
    clauseSat σ [(p, false), (q, false), (o, false)] := by
  rw [clauseSat_three]
  rcases Bool.eq_false_or_eq_true (σ p) with hp | hp <;>
    rcases Bool.eq_false_or_eq_true (σ q) with hq | hq <;> simp_all

lemma clauseSat_nand₂ {σ : Assign} {p q o : ℕ} (h : σ o = !(σ p && σ q)) :
    clauseSat σ [(p, true), (o, true)] := by
  rw [clauseSat_two]
  rcases Bool.eq_false_or_eq_true (σ p) with hp | hp <;>
    rcases Bool.eq_false_or_eq_true (σ q) with hq | hq <;> simp_all

lemma clauseSat_nand₃ {σ : Assign} {p q o : ℕ} (h : σ o = !(σ p && σ q)) :
    clauseSat σ [(q, true), (o, true)] := by
  rw [clauseSat_two]
  rcases Bool.eq_false_or_eq_true (σ p) with hp | hp <;>
    rcases Bool.eq_false_or_eq_true (σ q) with hq | hq <;> simp_all

/-! ### Circuits -/

/-- A gate of a straight-line Boolean program: a constant, a read of an input bit, or a
NAND of the values of two earlier gates.  A reference to a gate that is not strictly
earlier evaluates to `false`. -/
inductive Gate
  | const (b : Bool)
  | inp (j : ℕ)
  | nand (a b : ℕ)
deriving DecidableEq, Inhabited

/-- A circuit: a straight-line program together with the index of its output gate. -/
structure Circuit where
  gates : List Gate
  out : ℕ

/-- The value of gate number `k` of the straight-line program `gs` on inputs `inp`. -/
def gateVal (gs : List Gate) (inp : Assign) (k : ℕ) : Bool :=
  match gs[k]? with
  | none => false
  | some (Gate.const b) => b
  | some (Gate.inp j) => inp j
  | some (Gate.nand a b) =>
      !((if _h : a < k then gateVal gs inp a else false) &&
        (if _h : b < k then gateVal gs inp b else false))
termination_by k
decreasing_by all_goals omega

lemma gateVal_none {gs : List Gate} {inp : Assign} {k : ℕ} (h : gs[k]? = none) :
    gateVal gs inp k = false := by
  rw [gateVal, h]

lemma gateVal_const {gs : List Gate} {inp : Assign} {k : ℕ} {b : Bool}
    (h : gs[k]? = some (Gate.const b)) : gateVal gs inp k = b := by
  rw [gateVal, h]

lemma gateVal_inp {gs : List Gate} {inp : Assign} {k p : ℕ}
    (h : gs[k]? = some (Gate.inp p)) : gateVal gs inp k = inp p := by
  rw [gateVal, h]

lemma gateVal_nand {gs : List Gate} {inp : Assign} {k a b : ℕ}
    (h : gs[k]? = some (Gate.nand a b)) :
    gateVal gs inp k =
      !((if _h : a < k then gateVal gs inp a else false) &&
        (if _h : b < k then gateVal gs inp b else false)) := by
  rw [gateVal, h]

/-- The value computed by a circuit. -/
def evalCircuit (C : Circuit) (inp : Assign) : Bool := gateVal C.gates inp C.out

/-! ### Machines -/

/-- A sequential Boolean circuit machine: `width` configuration bits, an accepting bit
`acc`, and a circuit computing each next configuration bit from the current
configuration. -/
structure Machine where
  width : ℕ
  acc : ℕ
  step : ℕ → Circuit

/-- Configuration bits outside the machine's width are read as `false`. -/
def mask (M : Machine) (c : Assign) : Assign := fun p => if p < M.width then c p else false

/-- One step of the machine. -/
def stepConf (M : Machine) (c : Assign) : Assign :=
  fun j => if j < M.width then evalCircuit (M.step j) (mask M c) else false

/-- The configuration after `i` steps starting from `c₀`. -/
def conf (M : Machine) (c₀ : Assign) (i : ℕ) : Assign := (stepConf M)^[i] c₀

/-- The machine accepts `c₀` within `t` steps if the accepting bit is set at time `t`. -/
def Accepts (M : Machine) (c₀ : Assign) (t : ℕ) : Prop := mask M (conf M c₀ t) M.acc = true

/-- The language of a machine with time bound `tb`: the inputs `x` for which some
completion of `x` to a full initial configuration (the nondeterministic guess) is
accepted within `tb x.length` steps. -/
def lang (M : Machine) (tb : ℕ → ℕ) : Set (List Bool) :=
  {x | ∃ c₀ : Assign, (∀ p, p < x.length → c₀ p = x.getD p false) ∧
        Accepts M c₀ (tb x.length)}

/-! ### The tableau CNF -/

/-- A variable that is forced to be `false`. -/
def vFalse : ℕ := Nat.pair 2 0

/-- The variable for configuration bit `j` at time `i`. -/
def vCfg (i j : ℕ) : ℕ := Nat.pair 0 (Nat.pair i j)

/-- The Tseitin variable for gate `k` of the step circuit of output bit `j` at time `i`. -/
def vGate (i j k : ℕ) : ℕ := Nat.pair 1 (Nat.pair (Nat.pair i j) k)

/-- The variable holding the value of input bit `p` read at time `i`. -/
def vIn (M : Machine) (i p : ℕ) : ℕ := if p < M.width then vCfg i p else vFalse

/-- The variable holding the value of the reference `a` made by gate `k`. -/
def vRef (i j k a : ℕ) : ℕ := if a < k then vGate i j a else vFalse

/-- The variable holding the output value of the circuit `C` at time `i`, bit `j`. -/
def vOut (i j : ℕ) (C : Circuit) : ℕ :=
  if C.out < C.gates.length then vGate i j C.out else vFalse

/-- Tseitin clauses defining the variable of gate `k`. -/
def gateClauses (M : Machine) (i j k : ℕ) (g : Gate) : CNFFormula :=
  match g with
  | Gate.const b => [[(vGate i j k, b)]]
  | Gate.inp p =>
      [[(vGate i j k, false), (vIn M i p, true)], [(vGate i j k, true), (vIn M i p, false)]]
  | Gate.nand a b =>
      [[(vRef i j k a, false), (vRef i j k b, false), (vGate i j k, false)],
       [(vRef i j k a, true), (vGate i j k, true)],
       [(vRef i j k b, true), (vGate i j k, true)]]

/-- All clauses describing the computation of configuration bit `j` at time step `i`. -/
def stepClauses (M : Machine) (i j : ℕ) : CNFFormula :=
  ((List.range (M.step j).gates.length).flatMap
      (fun k => gateClauses M i j k ((M.step j).gates.getD k (Gate.const false))))
  ++ [[(vCfg (i + 1) j, false), (vOut i j (M.step j), true)],
      [(vCfg (i + 1) j, true), (vOut i j (M.step j), false)]]

/-- The Cook–Levin tableau CNF for machine `M`, input `x` and time bound `t`. -/
def tableau (M : Machine) (x : List Bool) (t : ℕ) : CNFFormula :=
  [[(vFalse, false)]]
  ++ (List.range x.length).map (fun p => [(vCfg 0 p, x.getD p false)])
  ++ (List.range t).flatMap
      (fun i => (List.range M.width).flatMap (fun j => stepClauses M i j))
  ++ [[(vIn M t M.acc, true)]]

/-! ### Basic simp lemmas about the variable encoding -/

lemma unpair_vFalse : Nat.unpair vFalse = (2, 0) := by simp [vFalse]

lemma unpair_vCfg (i j : ℕ) : Nat.unpair (vCfg i j) = (0, Nat.pair i j) := by simp [vCfg]

lemma unpair_vGate (i j k : ℕ) :
    Nat.unpair (vGate i j k) = (1, Nat.pair (Nat.pair i j) k) := by simp [vGate]

/-! ### The canonical assignment associated with a run -/

/-- The assignment read off from the actual run of `M` on initial configuration `c₀`. -/
def canon (M : Machine) (c₀ : Assign) : Assign := fun v =>
  match (Nat.unpair v).1 with
  | 0 => conf M c₀ (Nat.unpair (Nat.unpair v).2).1 (Nat.unpair (Nat.unpair v).2).2
  | 1 =>
      gateVal (M.step (Nat.unpair (Nat.unpair (Nat.unpair v).2).1).2).gates
        (mask M (conf M c₀ (Nat.unpair (Nat.unpair (Nat.unpair v).2).1).1))
        (Nat.unpair (Nat.unpair v).2).2
  | _ => false

lemma canon_vCfg (M : Machine) (c₀ : Assign) (i j : ℕ) :
    canon M c₀ (vCfg i j) = conf M c₀ i j := by
  simp [canon, unpair_vCfg]

lemma canon_vGate (M : Machine) (c₀ : Assign) (i j k : ℕ) :
    canon M c₀ (vGate i j k) = gateVal (M.step j).gates (mask M (conf M c₀ i)) k := by
  simp [canon, unpair_vGate]

lemma canon_vFalse (M : Machine) (c₀ : Assign) : canon M c₀ vFalse = false := by
  simp [canon, unpair_vFalse]

lemma canon_vIn (M : Machine) (c₀ : Assign) (i p : ℕ) :
    canon M c₀ (vIn M i p) = mask M (conf M c₀ i) p := by
  unfold vIn mask
  by_cases h : p < M.width <;> simp [h, canon_vCfg, canon_vFalse]

lemma canon_vRef (M : Machine) (c₀ : Assign) (i j k a : ℕ) :
    canon M c₀ (vRef i j k a) =
      (if _h : a < k then gateVal (M.step j).gates (mask M (conf M c₀ i)) a else false) := by
  unfold vRef
  by_cases h : a < k <;> simp [h, canon_vGate, canon_vFalse]

lemma canon_vOut (M : Machine) (c₀ : Assign) (i j : ℕ) :
    canon M c₀ (vOut i j (M.step j)) = evalCircuit (M.step j) (mask M (conf M c₀ i)) := by
  unfold vOut evalCircuit
  by_cases h : (M.step j).out < (M.step j).gates.length
  · rw [if_pos h, canon_vGate]
  · rw [if_neg h, canon_vFalse,
      gateVal_none (List.getElem?_eq_none_iff.mpr (by omega))]

/-! ### Membership lemmas for the tableau -/

lemma mem_tableau_false (M : Machine) (x : List Bool) (t : ℕ) :
    [(vFalse, false)] ∈ tableau M x t := by
  simp [tableau]

lemma mem_tableau_input (M : Machine) (x : List Bool) (t : ℕ) {p : ℕ} (hp : p < x.length) :
    [(vCfg 0 p, x.getD p false)] ∈ tableau M x t := by
  simp only [tableau, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inr ⟨p, hp, rfl⟩))

lemma mem_tableau_step (M : Machine) (x : List Bool) (t : ℕ) {i j : ℕ}
    (hi : i < t) (hj : j < M.width) {c : Clause} (hc : c ∈ stepClauses M i j) :
    c ∈ tableau M x t := by
  simp only [tableau, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inr ⟨i, hi, ⟨j, hj, hc⟩⟩)

lemma mem_tableau_accept (M : Machine) (x : List Bool) (t : ℕ) :
    [(vIn M t M.acc, true)] ∈ tableau M x t := by
  simp [tableau]

lemma mem_stepClauses_gate (M : Machine) (i j : ℕ) {k : ℕ}
    (hk : k < (M.step j).gates.length) {c : Clause}
    (hc : c ∈ gateClauses M i j k ((M.step j).gates.getD k (Gate.const false))) :
    c ∈ stepClauses M i j := by
  simp only [stepClauses, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl ⟨k, hk, hc⟩

lemma mem_stepClauses_link₁ (M : Machine) (i j : ℕ) :
    [(vCfg (i + 1) j, false), (vOut i j (M.step j), true)] ∈ stepClauses M i j := by
  rw [stepClauses]
  exact List.mem_append_right _ (List.Mem.head _)

lemma mem_stepClauses_link₂ (M : Machine) (i j : ℕ) :
    [(vCfg (i + 1) j, true), (vOut i j (M.step j), false)] ∈ stepClauses M i j := by
  rw [stepClauses]
  exact List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _))

/-! ### Boolean helper lemmas -/

lemma bool_eq_of_iff {σ : Assign} {u v : ℕ}
    (h₁ : σ u = false ∨ σ v = true) (h₂ : σ u = true ∨ σ v = false) : σ u = σ v := by
  rcases Bool.eq_false_or_eq_true (σ u) with hu | hu <;>
    rcases Bool.eq_false_or_eq_true (σ v) with hv | hv <;>
      simp_all

lemma bool_nand_of_clauses {σ : Assign} {p q o : ℕ}
    (h₁ : σ p = false ∨ σ q = false ∨ σ o = false)
    (h₂ : σ p = true ∨ σ o = true)
    (h₃ : σ q = true ∨ σ o = true) : σ o = !(σ p && σ q) := by
  rcases Bool.eq_false_or_eq_true (σ p) with hp | hp <;>
    rcases Bool.eq_false_or_eq_true (σ q) with hq | hq <;>
      rcases Bool.eq_false_or_eq_true (σ o) with ho | ho <;> simp_all

/-! ### One step of the run -/

lemma conf_succ (M : Machine) (c₀ : Assign) (i : ℕ) :
    conf M c₀ (i + 1) = stepConf M (conf M c₀ i) := by
  simp [conf, Function.iterate_succ_apply']

/-! ### Soundness: an accepting run yields a satisfying assignment -/

lemma canon_sat_gateClauses (M : Machine) (c₀ : Assign) (i j k : ℕ)
    (hk : k < (M.step j).gates.length) {c : Clause}
    (hc : c ∈ gateClauses M i j k ((M.step j).gates.getD k (Gate.const false))) :
    clauseSat (canon M c₀) c := by
  have hget : (M.step j).gates[k]? = some ((M.step j).gates.getD k (Gate.const false)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    simp
  cases hg : (M.step j).gates.getD k (Gate.const false) with
  | const b =>
      rw [hg] at hc hget
      simp only [gateClauses, List.mem_singleton] at hc
      subst hc
      rw [clauseSat_one, canon_vGate, gateVal_const hget]
  | inp p =>
      rw [hg] at hc hget
      have hval : canon M c₀ (vGate i j k) = canon M c₀ (vIn M i p) := by
        rw [canon_vGate, canon_vIn, gateVal_inp hget]
      simp only [gateClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact clauseSat_eq₁ hval
      · exact clauseSat_eq₂ hval
  | nand a b =>
      rw [hg] at hc hget
      have hval : canon M c₀ (vGate i j k) =
          !(canon M c₀ (vRef i j k a) && canon M c₀ (vRef i j k b)) := by
        rw [canon_vGate, canon_vRef, canon_vRef, gateVal_nand hget]
      simp only [gateClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact clauseSat_nand₁ hval
      · exact clauseSat_nand₂ hval
      · exact clauseSat_nand₃ hval

lemma canon_sat_stepClauses (M : Machine) (c₀ : Assign) (i j : ℕ) (hj : j < M.width)
    {c : Clause} (hc : c ∈ stepClauses M i j) : clauseSat (canon M c₀) c := by
  have hlink : canon M c₀ (vCfg (i + 1) j) = canon M c₀ (vOut i j (M.step j)) := by
    rw [canon_vCfg, canon_vOut, conf_succ, stepConf, if_pos hj]
  simp only [stepClauses, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with ⟨k, hk, hc⟩ | rfl | rfl
  · exact canon_sat_gateClauses M c₀ i j k hk hc
  · exact clauseSat_eq₁ hlink
  · exact clauseSat_eq₂ hlink

lemma canon_sat_tableau (M : Machine) (x : List Bool) (t : ℕ) (c₀ : Assign)
    (hx : ∀ p, p < x.length → c₀ p = x.getD p false) (hacc : Accepts M c₀ t) :
    ∀ c ∈ tableau M x t, clauseSat (canon M c₀) c := by
  intro c hc
  simp only [tableau, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_singleton] at hc
  rcases hc with ((rfl | ⟨p, hp, rfl⟩) | ⟨i, hi, ⟨j, hj, hc⟩⟩) | rfl
  · rw [clauseSat_one, canon_vFalse]
  · rw [clauseSat_one, canon_vCfg]
    simpa [conf] using hx p hp
  · exact canon_sat_stepClauses M c₀ i j hj hc
  · rw [clauseSat_one, canon_vIn]
    exact hacc

/-! ### Completeness: a satisfying assignment yields an accepting run -/

section Complete

variable {M : Machine} {x : List Bool} {t : ℕ} {σ : Assign}

/-- The initial configuration read off from a satisfying assignment. -/
private def c₀of (σ : Assign) : Assign := fun p => σ (vCfg 0 p)

private lemma sigma_false (hσ : ∀ c ∈ tableau M x t, clauseSat σ c) : σ vFalse = false := by
  have := hσ _ (mem_tableau_false M x t)
  rwa [clauseSat_one] at this

private lemma sigma_gate (hσ : ∀ c ∈ tableau M x t, clauseSat σ c) {i j : ℕ}
    (hi : i < t) (hj : j < M.width)
    (hcfg : ∀ p, p < M.width → σ (vCfg i p) = conf M (c₀of σ) i p) :
    ∀ k, k < (M.step j).gates.length →
      σ (vGate i j k) = gateVal (M.step j).gates (mask M (conf M (c₀of σ) i)) k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hget : (M.step j).gates[k]? =
        some ((M.step j).gates.getD k (Gate.const false)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      simp
    have hin : ∀ c ∈ gateClauses M i j k ((M.step j).gates.getD k (Gate.const false)),
        clauseSat σ c := by
      intro c hc
      exact hσ _ (mem_tableau_step M x t hi hj (mem_stepClauses_gate M i j hk hc))
    have href : ∀ a, σ (vRef i j k a) =
        (if _h : a < k then gateVal (M.step j).gates (mask M (conf M (c₀of σ) i)) a
          else false) := by
      intro a
      by_cases ha : a < k
      · rw [vRef, if_pos ha, dif_pos ha]
        exact ih a ha (by omega)
      · rw [vRef, if_neg ha, dif_neg ha]
        exact sigma_false hσ
    cases hg : (M.step j).gates.getD k (Gate.const false) with
    | const b =>
        rw [hg] at hget
        have h := hin [(vGate i j k, b)] (by rw [hg]; simp [gateClauses])
        rw [clauseSat_one] at h
        rw [h, gateVal_const hget]
    | inp p =>
        rw [hg] at hget
        have h₁ := hin [(vGate i j k, false), (vIn M i p, true)] (by
          rw [hg]; simp [gateClauses])
        have h₂ := hin [(vGate i j k, true), (vIn M i p, false)] (by
          rw [hg]; simp [gateClauses])
        rw [clauseSat_two] at h₁ h₂
        have heq : σ (vGate i j k) = σ (vIn M i p) := bool_eq_of_iff h₁ h₂
        have hvin : σ (vIn M i p) = mask M (conf M (c₀of σ) i) p := by
          unfold vIn mask
          by_cases hp : p < M.width
          · rw [if_pos hp, if_pos hp]
            exact hcfg p hp
          · rw [if_neg hp, if_neg hp]
            exact sigma_false hσ
        rw [gateVal_inp hget, heq, hvin]
    | nand a b =>
        rw [hg] at hget
        have h₁ := hin [(vRef i j k a, false), (vRef i j k b, false), (vGate i j k, false)]
          (by rw [hg]; simp [gateClauses])
        have h₂ := hin [(vRef i j k a, true), (vGate i j k, true)] (by
          rw [hg]; simp [gateClauses])
        have h₃ := hin [(vRef i j k b, true), (vGate i j k, true)] (by
          rw [hg]; simp [gateClauses])
        rw [clauseSat_three] at h₁
        rw [clauseSat_two] at h₂ h₃
        have hnand := bool_nand_of_clauses h₁ h₂ h₃
        rw [gateVal_nand hget, hnand, href a, href b]

private lemma sigma_out (hσ : ∀ c ∈ tableau M x t, clauseSat σ c) {i j : ℕ}
    (hi : i < t) (hj : j < M.width)
    (hcfg : ∀ p, p < M.width → σ (vCfg i p) = conf M (c₀of σ) i p) :
    σ (vOut i j (M.step j)) = evalCircuit (M.step j) (mask M (conf M (c₀of σ) i)) := by
  unfold vOut evalCircuit
  by_cases h : (M.step j).out < (M.step j).gates.length
  · rw [if_pos h]
    exact sigma_gate hσ hi hj hcfg _ h
  · rw [if_neg h, gateVal_none (List.getElem?_eq_none_iff.mpr (by omega))]
    exact sigma_false hσ

private lemma sigma_conf (hσ : ∀ c ∈ tableau M x t, clauseSat σ c) :
    ∀ i, i ≤ t → ∀ p, p < M.width → σ (vCfg i p) = conf M (c₀of σ) i p := by
  intro i
  induction i with
  | zero => intro _ p _; rfl
  | succ i ih =>
    intro hi p hp
    have hi' : i < t := by omega
    have hcfg := ih (by omega)
    have hlink₁ := hσ _ (mem_tableau_step M x t hi' hp (mem_stepClauses_link₁ M i p))
    have hlink₂ := hσ _ (mem_tableau_step M x t hi' hp (mem_stepClauses_link₂ M i p))
    rw [clauseSat_two] at hlink₁ hlink₂
    have heq : σ (vCfg (i + 1) p) = σ (vOut i p (M.step p)) := bool_eq_of_iff hlink₁ hlink₂
    rw [heq, sigma_out hσ hi' hp hcfg, conf_succ, stepConf, if_pos hp]

private lemma sigma_accepts (hσ : ∀ c ∈ tableau M x t, clauseSat σ c) :
    Accepts M (c₀of σ) t := by
  have hacc := hσ _ (mem_tableau_accept M x t)
  rw [clauseSat_one] at hacc
  unfold Accepts mask
  by_cases h : M.acc < M.width
  · rw [if_pos h, ← sigma_conf hσ t le_rfl M.acc h]
    rw [vIn, if_pos h] at hacc
    exact hacc
  · rw [vIn, if_neg h] at hacc
    rw [sigma_false hσ] at hacc
    exact absurd hacc (by simp)

private lemma sigma_input (hσ : ∀ c ∈ tableau M x t, clauseSat σ c) :
    ∀ p, p < x.length → c₀of σ p = x.getD p false := by
  intro p hp
  have := hσ _ (mem_tableau_input M x t hp)
  rw [clauseSat_one] at this
  exact this

end Complete

/-! ### The main theorem -/

/-- **Cook–Levin (core reduction).**  For a sequential Boolean circuit machine `M`, an
input `x` and a time bound `t`, the explicitly constructed tableau CNF `tableau M x t` is
satisfiable if and only if some completion of `x` to an initial configuration (i.e. some
nondeterministic guess) is accepted by `M` within `t` steps. -/
theorem cook_levin_tableau (M : Machine) (x : List Bool) (t : ℕ) :
    Sat (tableau M x t) ↔
      ∃ c₀ : Assign, (∀ p, p < x.length → c₀ p = x.getD p false) ∧ Accepts M c₀ t := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨c₀of σ, sigma_input hσ, sigma_accepts hσ⟩
  · rintro ⟨c₀, hx, hacc⟩
    exact ⟨canon M c₀, canon_sat_tableau M x t c₀ hx hacc⟩

/-- **Cook–Levin.**  The explicit map `x ↦ tableau M x (tb x.length)` is a many-one
reduction of the language of any time-`tb` bounded nondeterministic machine to `SAT`.
Together with `Frontier.tableau_length_le` (which bounds the size of the produced formula
polynomially in the running time, the width and the circuit sizes) this says that `SAT`
is NP-hard; `Frontier.sat_iff_short_witness` is the corresponding membership statement,
namely that satisfiability is witnessed by an assignment of size linear in the formula and
checked by the explicit linear-time evaluator `Frontier.cnfEval`. -/
theorem cook_levin (M : Machine) (tb : ℕ → ℕ) (x : List Bool) :
    x ∈ lang M tb ↔ tableau M x (tb x.length) ∈ SAT := by
  rw [SAT, Set.mem_setOf_eq, cook_levin_tableau]
  rfl

/-! ### Size of the reduction -/

lemma length_gateClauses (M : Machine) (i j k : ℕ) (g : Gate) :
    (gateClauses M i j k g).length ≤ 3 := by
  cases g <;> simp [gateClauses]

lemma length_stepClauses_le (M : Machine) (i j g : ℕ)
    (hg : (M.step j).gates.length ≤ g) : (stepClauses M i j).length ≤ 3 * g + 2 := by
  have h₁ : ((List.range (M.step j).gates.length).flatMap
      (fun k => gateClauses M i j k ((M.step j).gates.getD k (Gate.const false)))).length
      ≤ 3 * g := by
    rw [List.length_flatMap]
    calc ((List.range (M.step j).gates.length).map
            (fun k => (gateClauses M i j k
              ((M.step j).gates.getD k (Gate.const false))).length)).sum
        ≤ ((List.range (M.step j).gates.length).map (fun _ => 3)).sum := by
          apply List.sum_le_sum
          intro k _
          exact length_gateClauses M i j k _
      _ = (M.step j).gates.length * 3 := by
          simp [List.map_const', List.sum_replicate, smul_eq_mul]
      _ ≤ 3 * g := by omega
  have h₂ : (stepClauses M i j).length =
      ((List.range (M.step j).gates.length).flatMap
        (fun k => gateClauses M i j k ((M.step j).gates.getD k (Gate.const false)))).length
        + 2 := by
    simp [stepClauses]
  omega

/-- The size of the reduction: the tableau has at most `2 + |x| + t · width · (3g + 2)`
clauses, where `g` bounds the number of gates of each step circuit.  In particular the
reduction produces polynomial-size formulas whenever the time bound, the width and the
circuit sizes are polynomial. -/
theorem tableau_length_le (M : Machine) (x : List Bool) (t g : ℕ)
    (hg : ∀ j, j < M.width → (M.step j).gates.length ≤ g) :
    (tableau M x t).length ≤ 2 + x.length + t * (M.width * (3 * g + 2)) := by
  have hinner : ∀ i, ((List.range M.width).flatMap (fun j => stepClauses M i j)).length
      ≤ M.width * (3 * g + 2) := by
    intro i
    rw [List.length_flatMap]
    calc ((List.range M.width).map (fun j => (stepClauses M i j).length)).sum
        ≤ ((List.range M.width).map (fun _ => 3 * g + 2)).sum := by
          apply List.sum_le_sum
          intro j hj
          rw [List.mem_range] at hj
          exact length_stepClauses_le M i j g (hg j hj)
      _ = M.width * (3 * g + 2) := by
          simp [List.map_const', List.sum_replicate, smul_eq_mul]
  have houter : ((List.range t).flatMap
      (fun i => (List.range M.width).flatMap (fun j => stepClauses M i j))).length
      ≤ t * (M.width * (3 * g + 2)) := by
    rw [List.length_flatMap]
    calc ((List.range t).map
            (fun i => ((List.range M.width).flatMap (fun j => stepClauses M i j)).length)).sum
        ≤ ((List.range t).map (fun _ => M.width * (3 * g + 2))).sum := by
          apply List.sum_le_sum
          intro i _
          exact hinner i
      _ = t * (M.width * (3 * g + 2)) := by
          simp [List.map_const', List.sum_replicate, smul_eq_mul]
  have hlen : (tableau M x t).length = 1 + x.length +
      ((List.range t).flatMap
        (fun i => (List.range M.width).flatMap (fun j => stepClauses M i j))).length + 1 := by
    simp only [tableau, List.length_append, List.length_map, List.length_range,
      List.length_cons, List.length_nil]
  omega

/-! ### Sanity checks: the reduction is not vacuous

`copyMachine` copies configuration bit `0` to itself, so it accepts exactly the inputs
starting with `true`; `guessMachine` copies the (unconstrained, i.e. guessed) bit `1` into
the accepting bit `0`, so on the empty input it accepts thanks to a nondeterministic
guess. -/

/-- A one-bit machine that keeps its accepting bit unchanged. -/
def copyMachine : Machine := ⟨1, 0, fun _ => ⟨[Gate.inp 0], 0⟩⟩

example : Sat (tableau copyMachine [true] 1) := by
  rw [cook_levin_tableau]
  refine ⟨fun _ => true, ?_, ?_⟩
  · intro p hp
    have hp0 : p = 0 := by simp only [List.length_singleton] at hp; omega
    subst hp0
    rfl
  · simp [Accepts, conf, stepConf, mask, evalCircuit, gateVal, copyMachine]

example : ¬ Sat (tableau copyMachine [false] 1) := by
  rw [cook_levin_tableau]
  rintro ⟨c₀, hx, hacc⟩
  have h0 : c₀ 0 = false := hx 0 (by simp)
  simp [Accepts, conf, stepConf, mask, evalCircuit, gateVal, copyMachine, h0] at hacc

/-- A two-bit machine whose accepting bit is the guessed bit `1`. -/
def guessMachine : Machine :=
  ⟨2, 0, fun j => if j = 0 then ⟨[Gate.inp 1], 0⟩ else ⟨[Gate.const false], 0⟩⟩

example : Sat (tableau guessMachine [] 1) := by
  rw [cook_levin_tableau]
  refine ⟨fun _ => true, ?_, ?_⟩
  · intro p hp
    simp at hp
  · simp [Accepts, conf, stepConf, mask, evalCircuit, gateVal, guessMachine]

/-! ### Short, efficiently checkable witnesses for `SAT`

This is the (easy) membership half of NP-completeness: a satisfiable CNF has a witness of
size linear in the formula (a truth value for each of its variables), and the witness is
verified by the explicit Boolean evaluator `cnfEval`, which runs in time linear in the
size of the formula. -/

/-- Boolean evaluation of a clause. -/
def clauseEval (σ : Assign) (c : Clause) : Bool := c.any fun l => σ l.1 == l.2

/-- Boolean evaluation of a CNF formula. -/
def cnfEval (σ : Assign) (φ : CNFFormula) : Bool := φ.all (clauseEval σ)

lemma clauseEval_eq_true_iff (σ : Assign) (c : Clause) :
    clauseEval σ c = true ↔ clauseSat σ c := by
  simp [clauseEval, clauseSat]

lemma cnfEval_eq_true_iff (σ : Assign) (φ : CNFFormula) :
    cnfEval σ φ = true ↔ ∀ c ∈ φ, clauseSat σ c := by
  simp [cnfEval, clauseEval_eq_true_iff]

/-- An upper bound for the variables occurring in a formula. -/
def maxVar (φ : CNFFormula) : ℕ := (φ.flatMap fun c => c.map Prod.fst).foldr max 0

lemma le_foldr_max (L : List ℕ) {a : ℕ} (ha : a ∈ L) : a ≤ L.foldr max 0 := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
      rcases List.mem_cons.mp ha with rfl | ha'
      · simp
      · exact le_trans (ih ha') (by simp)

lemma le_maxVar {φ : CNFFormula} {c : Clause} {l : Lit} (hc : c ∈ φ) (hl : l ∈ c) :
    l.1 ≤ maxVar φ := by
  apply le_foldr_max
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨c, hc, ⟨l, hl, rfl⟩⟩

/-- **`SAT` has short, linear-time checkable witnesses.**  A CNF formula is satisfiable
iff there is a list of truth values, one for each variable index up to `maxVar φ`, on
which the explicit evaluator `cnfEval` returns `true`. -/
theorem sat_iff_short_witness (φ : CNFFormula) :
    Sat φ ↔ ∃ w : List Bool, w.length = maxVar φ + 1 ∧
      cnfEval (fun v => w.getD v false) φ = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨(List.range (maxVar φ + 1)).map σ, by simp, ?_⟩
    rw [cnfEval_eq_true_iff]
    intro c hc
    obtain ⟨l, hl, hlv⟩ := hσ c hc
    refine ⟨l, hl, ?_⟩
    have hlt : l.1 < maxVar φ + 1 := Nat.lt_succ_of_le (le_maxVar hc hl)
    show (List.map σ (List.range (maxVar φ + 1))).getD l.1 false = l.2
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
    simpa using hlv
  · rintro ⟨w, -, hw⟩
    exact ⟨fun v => w.getD v false, (cnfEval_eq_true_iff _ _).mp hw⟩

end Frontier

