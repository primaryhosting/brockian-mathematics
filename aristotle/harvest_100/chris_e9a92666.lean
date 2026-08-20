/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.BGSModel

/-!
## Basic properties of the machine model

* costs and query lists only grow;
* the cost of a run does not depend on the cost already accumulated (`run_shift`);
* every recorded query has length at most the cost, and there are at most `cost`
  many queries (`run_QInv`);
* locality: a run only depends on the oracle at the strings it queries
  (`run_local`).
-/

namespace CS.BGS

variable {O O' : Oracle} {st : State} {i : ℕ} {s : Str} {a b c e : Expr}

/-! ### Unfolding lemmas -/

@[simp] lemma evalE_var : evalE O (.var i) st = (st.vars i, { st with cost := st.cost + 1 }) := rfl

@[simp] lemma evalE_lit :
    evalE O (.lit s) st = (s, { st with cost := st.cost + s.length + 1 }) := rfl

@[simp] lemma evalE_cat : evalE O (.cat a b) st =
    ((evalE O a st).1 ++ (evalE O b (evalE O a st).2).1,
      { (evalE O b (evalE O a st).2).2 with
        cost := (evalE O b (evalE O a st).2).2.cost + (evalE O a st).1.length
          + (evalE O b (evalE O a st).2).1.length + 1 }) := rfl

@[simp] lemma evalE_smash : evalE O (.smash a b) st =
    (List.replicate ((evalE O a st).1.length * (evalE O b (evalE O a st).2).1.length) false,
      { (evalE O b (evalE O a st).2).2 with
        cost := (evalE O b (evalE O a st).2).2.cost
          + (evalE O a st).1.length * (evalE O b (evalE O a st).2).1.length + 1 }) := rfl

@[simp] lemma evalE_tail : evalE O (.tail a) st =
    ((evalE O a st).1.tail, { (evalE O a st).2 with cost := (evalE O a st).2.cost + 1 }) := rfl

@[simp] lemma evalE_eqE : evalE O (.eqE a b) st =
    ((if (evalE O a st).1 = (evalE O b (evalE O a st).2).1 then [true] else []),
      { (evalE O b (evalE O a st).2).2 with
        cost := (evalE O b (evalE O a st).2).2.cost + (evalE O a st).1.length
          + (evalE O b (evalE O a st).2).1.length + 1 }) := rfl

@[simp] lemma evalE_query : evalE O (.query a) st =
    ((if O (evalE O a st).1 then [true] else []),
      { (evalE O a st).2 with cost := (evalE O a st).2.cost + (evalE O a st).1.length + 1,
        qs := (evalE O a st).1 :: (evalE O a st).2.qs }) := rfl

@[simp] lemma run_skip : run O .skip st = { st with cost := st.cost + 1 } := rfl

@[simp] lemma run_assign : run O (.assign i e) st =
    { (evalE O e st).2 with vars := upd (evalE O e st).2.vars i (evalE O e st).1,
      cost := (evalE O e st).2.cost + (evalE O e st).1.length + 1 } := rfl

@[simp] lemma run_seq {p q : Prog} : run O (.seq p q) st = run O q (run O p st) := rfl

lemma run_ite {t f : Prog} : run O (.ite c t f) st =
    if (evalE O c st).1 = [] then run O f { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 }
    else run O t { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 } := rfl

lemma run_loop {body : Prog} : run O (.loop c body) st =
    (run O body)^[(evalE O c st).1.length]
      { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 } := rfl

/-! ### Monotonicity of cost -/

lemma evalE_cost_mono (O : Oracle) (e : Expr) (st : State) :
    st.cost ≤ (evalE O e st).2.cost := by
  induction e generalizing st with
  | var i => simp
  | lit s => simp
  | cat a b iha ihb =>
      have h1 := iha st; have h2 := ihb (evalE O a st).2
      simp only [evalE_cat]; omega
  | smash a b iha ihb =>
      have h1 := iha st; have h2 := ihb (evalE O a st).2
      simp only [evalE_smash]; omega
  | tail a iha => have h1 := iha st; simp only [evalE_tail]; omega
  | eqE a b iha ihb =>
      have h1 := iha st; have h2 := ihb (evalE O a st).2
      simp only [evalE_eqE]; omega
  | query a iha => have h1 := iha st; simp only [evalE_query]; omega

lemma iter_cost_mono (O : Oracle) (body : Prog)
    (ih : ∀ s : State, s.cost ≤ (run O body s).cost) (n : ℕ) (s : State) :
    s.cost ≤ ((run O body)^[n] s).cost := by
  induction n generalizing s with
  | zero => simp
  | succ n ihn => rw [Function.iterate_succ_apply]; exact le_trans (ih s) (ihn _)

lemma run_cost_mono (O : Oracle) (p : Prog) (st : State) :
    st.cost ≤ (run O p st).cost := by
  induction p generalizing st with
  | skip => simp
  | assign i e => have h1 := evalE_cost_mono O e st; simp only [run_assign]; omega
  | seq p q ihp ihq => have h1 := ihp st; have h2 := ihq (run O p st); simp only [run_seq]; omega
  | ite c t f iht ihf =>
      have h1 := evalE_cost_mono O c st
      rw [run_ite]
      split
      · have h2 := ihf { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 }
        simp only at h2; omega
      · have h2 := iht { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 }
        simp only at h2; omega
  | loop c body ih =>
      have h1 := evalE_cost_mono O c st
      rw [run_loop]
      have h2 := iter_cost_mono O body ih (evalE O c st).1.length
        { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 }
      simp only at h2; omega

/-! ### Monotonicity of the query list -/

lemma evalE_qs_mono (O : Oracle) (e : Expr) (st : State) : st.qs ⊆ (evalE O e st).2.qs := by
  induction e generalizing st with
  | var i => simp
  | lit s => simp
  | cat a b iha ihb =>
      have h1 := iha st; have h2 := ihb (evalE O a st).2
      simp only [evalE_cat]; exact h1.trans h2
  | smash a b iha ihb =>
      have h1 := iha st; have h2 := ihb (evalE O a st).2
      simp only [evalE_smash]; exact h1.trans h2
  | tail a iha => simpa using iha st
  | eqE a b iha ihb =>
      have h1 := iha st; have h2 := ihb (evalE O a st).2
      simp only [evalE_eqE]; exact h1.trans h2
  | query a iha =>
      have h1 := iha st
      simp only [evalE_query]
      exact fun q hq => List.mem_cons_of_mem _ (h1 hq)

lemma iter_qs_mono (O : Oracle) (body : Prog) (ih : ∀ s : State, s.qs ⊆ (run O body s).qs)
    (n : ℕ) (s : State) : s.qs ⊆ ((run O body)^[n] s).qs := by
  induction n generalizing s with
  | zero => simp
  | succ n ihn => rw [Function.iterate_succ_apply]; exact (ih s).trans (ihn _)

lemma run_qs_mono (O : Oracle) (p : Prog) (st : State) : st.qs ⊆ (run O p st).qs := by
  induction p generalizing st with
  | skip => simp
  | assign i e => simpa using evalE_qs_mono O e st
  | seq p q ihp ihq => exact (ihp st).trans (ihq (run O p st))
  | ite c t f iht ihf =>
      have h1 := evalE_qs_mono O c st
      rw [run_ite]
      split
      · exact h1.trans (ihf _)
      · exact h1.trans (iht _)
  | loop c body ih =>
      have h1 := evalE_qs_mono O c st
      rw [run_loop]
      exact h1.trans (iter_qs_mono O body ih _ _)

/-! ### Cost shifting -/

/-- Shift the accumulated cost of a state. -/
def shiftSt (st : State) (d : ℕ) : State := { st with cost := st.cost + d }

@[simp] lemma shiftSt_vars (st : State) (d : ℕ) : (shiftSt st d).vars = st.vars := rfl
@[simp] lemma shiftSt_qs (st : State) (d : ℕ) : (shiftSt st d).qs = st.qs := rfl
@[simp] lemma shiftSt_cost (st : State) (d : ℕ) : (shiftSt st d).cost = st.cost + d := rfl

lemma evalE_shift (O : Oracle) (e : Expr) (st : State) (d : ℕ) :
    evalE O e (shiftSt st d) = ((evalE O e st).1, shiftSt (evalE O e st).2 d) := by
  induction e generalizing st with
  | var i => simp [shiftSt]
  | lit s => simp [shiftSt]; omega
  | cat a b iha ihb => simp [shiftSt, iha, ihb]; omega
  | smash a b iha ihb => simp [shiftSt, iha, ihb]; omega
  | tail a iha => simp [shiftSt, iha]; omega
  | eqE a b iha ihb => simp [shiftSt, iha, ihb]; omega
  | query a iha => simp [shiftSt, iha]; omega

lemma iter_shift (O : Oracle) (body : Prog)
    (ih : ∀ (s : State) (d : ℕ), run O body (shiftSt s d) = shiftSt (run O body s) d)
    (n : ℕ) (s : State) (d : ℕ) :
    (run O body)^[n] (shiftSt s d) = shiftSt ((run O body)^[n] s) d := by
  induction n generalizing s with
  | zero => simp
  | succ n ihn => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, ihn]

lemma run_shift (O : Oracle) (p : Prog) (st : State) (d : ℕ) :
    run O p (shiftSt st d) = shiftSt (run O p st) d := by
  induction p generalizing st with
  | skip => simp [shiftSt]; omega
  | assign i e => simp [shiftSt, evalE_shift]; omega
  | seq p q ihp ihq => simp only [run_seq, ihp, ihq]
  | ite c t f iht ihf =>
      rw [run_ite, run_ite, evalE_shift]
      have key : ({ shiftSt (evalE O c st).2 d with
            cost := (shiftSt (evalE O c st).2 d).cost + 1 } : State)
          = shiftSt { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 } d := by
        simp [shiftSt]; omega
      simp only [key]
      split
      · exact ihf _ _
      · exact iht _ _
  | loop c body ih =>
      rw [run_loop, run_loop, evalE_shift]
      have key : ({ shiftSt (evalE O c st).2 d with
            cost := (shiftSt (evalE O c st).2 d).cost + 1 } : State)
          = shiftSt { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 } d := by
        simp [shiftSt]; omega
      simp only [key]
      exact iter_shift O body (fun s d => ih s) _ _ _

/-! ### The cost bounds the queries -/

/-- Invariant: every recorded query is no longer than the cost so far, and there are
at most `cost` many recorded queries. -/
def QInv (st : State) : Prop :=
  (∀ q ∈ st.qs, q.length ≤ st.cost) ∧ st.qs.length ≤ st.cost

lemma QInv_up {st : State} {v : ℕ → Str} {n : ℕ} (h : QInv st) (hc : st.cost ≤ n) :
    QInv { st with vars := v, cost := n } :=
  ⟨fun q hq => le_trans (h.1 q hq) hc, le_trans h.2 hc⟩

lemma QInv_up' {st : State} {n : ℕ} (h : QInv st) (hc : st.cost ≤ n) :
    QInv { st with cost := n } :=
  ⟨fun q hq => le_trans (h.1 q hq) hc, le_trans h.2 hc⟩

lemma evalE_QInv (O : Oracle) (e : Expr) (st : State) (h : QInv st) : QInv (evalE O e st).2 := by
  induction e generalizing st with
  | var i => exact QInv_up' h (by omega)
  | lit s => exact QInv_up' h (by omega)
  | cat a b iha ihb =>
      simp only [evalE_cat]
      exact QInv_up' (ihb _ (iha _ h)) (by omega)
  | smash a b iha ihb =>
      simp only [evalE_smash]
      exact QInv_up' (ihb _ (iha _ h)) (by omega)
  | tail a iha =>
      simp only [evalE_tail]
      exact QInv_up' (iha _ h) (by omega)
  | eqE a b iha ihb =>
      simp only [evalE_eqE]
      exact QInv_up' (ihb _ (iha _ h)) (by omega)
  | query a iha =>
      have h1 := iha _ h
      simp only [evalE_query]
      refine ⟨fun q hq => ?_, ?_⟩
      · simp only at hq ⊢
        rcases List.mem_cons.mp hq with rfl | hq
        · omega
        · have := h1.1 q hq; omega
      · simp only [List.length_cons]
        have := h1.2
        omega

lemma iter_QInv (O : Oracle) (body : Prog) (ih : ∀ s : State, QInv s → QInv (run O body s))
    (n : ℕ) (s : State) (hs : QInv s) : QInv ((run O body)^[n] s) := by
  induction n generalizing s with
  | zero => simpa using hs
  | succ n ihn => rw [Function.iterate_succ_apply]; exact ihn _ (ih _ hs)

lemma run_QInv (O : Oracle) (p : Prog) (st : State) (h : QInv st) : QInv (run O p st) := by
  induction p generalizing st with
  | skip => exact QInv_up' h (by omega)
  | assign i e =>
      have h1 := evalE_QInv O e st h
      simp only [run_assign]
      exact QInv_up h1 (by omega)
  | seq p q ihp ihq => exact ihq _ (ihp _ h)
  | ite c t f iht ihf =>
      have h1 := evalE_QInv O c st h
      rw [run_ite]
      have h2 : QInv { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 } :=
        QInv_up' h1 (by omega)
      split
      · exact ihf _ h2
      · exact iht _ h2
  | loop c body ih =>
      have h1 := evalE_QInv O c st h
      rw [run_loop]
      have h2 : QInv { (evalE O c st).2 with cost := (evalE O c st).2.cost + 1 } :=
        QInv_up' h1 (by omega)
      exact iter_QInv O body ih _ _ h2

/-! ### Locality -/

lemma evalE_local {O O' : Oracle} (e : Expr) (st : State)
    (h : ∀ q ∈ (evalE O e st).2.qs, O' q = O q) : evalE O' e st = evalE O e st := by
  induction e generalizing st with
  | var i => simp
  | lit s => simp
  | cat a b iha ihb =>
      have ha : evalE O' a st = evalE O a st := by
        refine iha st (fun q hq => h q ?_)
        exact (evalE_qs_mono O b (evalE O a st).2) hq
      have hb : evalE O' b (evalE O a st).2 = evalE O b (evalE O a st).2 :=
        ihb _ (fun q hq => h q hq)
      simp only [evalE_cat, ha, hb]
  | smash a b iha ihb =>
      have ha : evalE O' a st = evalE O a st := by
        refine iha st (fun q hq => h q ?_)
        exact (evalE_qs_mono O b (evalE O a st).2) hq
      have hb : evalE O' b (evalE O a st).2 = evalE O b (evalE O a st).2 :=
        ihb _ (fun q hq => h q hq)
      simp only [evalE_smash, ha, hb]
  | tail a iha =>
      have ha : evalE O' a st = evalE O a st := iha st (fun q hq => h q hq)
      simp only [evalE_tail, ha]
  | eqE a b iha ihb =>
      have ha : evalE O' a st = evalE O a st := by
        refine iha st (fun q hq => h q ?_)
        exact (evalE_qs_mono O b (evalE O a st).2) hq
      have hb : evalE O' b (evalE O a st).2 = evalE O b (evalE O a st).2 :=
        ihb _ (fun q hq => h q hq)
      simp only [evalE_eqE, ha, hb]
  | query a iha =>
      have ha : evalE O' a st = evalE O a st := by
        refine iha st (fun q hq => h q ?_)
        simp only [evalE_query]
        exact List.mem_cons_of_mem _ hq
      have hO : O' (evalE O a st).1 = O (evalE O a st).1 := by
        refine h _ ?_
        simp only [evalE_query]
        exact List.mem_cons_self
      simp only [evalE_query, ha, hO]

lemma run_local {O O' : Oracle} (p : Prog) (st : State)
    (h : ∀ q ∈ (run O p st).qs, O' q = O q) : run O' p st = run O p st := by
  induction p generalizing st with
  | skip => simp
  | assign i e =>
      have := evalE_local (O := O) (O' := O') e st (fun q hq => h q (by simpa using hq))
      simp only [run_assign, this]
  | seq p q ihp ihq =>
      have ha : run O' p st = run O p st := by
        refine ihp st (fun q hq => h q ?_)
        exact run_qs_mono O q (run O p st) hq
      simp only [run_seq, ha]
      exact ihq (run O p st) (fun q hq => h q hq)
  | ite c t f iht ihf =>
      have hc : evalE O' c st = evalE O c st := by
        refine evalE_local c st (fun q hq => h q ?_)
        rw [run_ite]
        split
        · exact run_qs_mono O f _ hq
        · exact run_qs_mono O t _ hq
      rw [run_ite, run_ite, hc]
      rw [run_ite] at h
      split
      · exact ihf _ (fun q hq => h q (by simp_all))
      · exact iht _ (fun q hq => h q (by simp_all))
  | loop c body ih =>
      have hmono : ∀ (m : ℕ) (s' : State), s'.qs ⊆ ((run O body)^[m] s').qs :=
        fun m s' => iter_qs_mono O body (run_qs_mono O body) m s'
      have key : ∀ (n : ℕ) (s : State), (∀ q ∈ ((run O body)^[n] s).qs, O' q = O q) →
          (run O' body)^[n] s = (run O body)^[n] s := by
        intro n
        induction n with
        | zero => intro s _; simp
        | succ n ihn =>
            intro s hs
            rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
            have h1 : run O' body s = run O body s := by
              refine ih s (fun q hq => hs q ?_)
              rw [Function.iterate_succ_apply]
              exact hmono n (run O body s) hq
            rw [h1]
            refine ihn _ (fun q hq => hs q ?_)
            rw [Function.iterate_succ_apply]
            exact hq
      have hc : evalE O' c st = evalE O c st := by
        refine evalE_local c st (fun q hq => h q ?_)
        rw [run_loop]
        exact hmono _ _ hq
      rw [run_loop, run_loop, hc]
      refine key _ _ (fun q hq => h q ?_)
      rw [run_loop]
      exact hq

end CS.BGS

/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## A model of polynomial-time oracle computation

We fix a concrete, self-contained machine model: a small imperative language over
bit strings with variables, concatenation, the "smash" function
`x # y = 0^(|x|·|y|)`, string equality, bounded iteration (`loop`), conditionals,
and an oracle query primitive.  Every operation is charged a cost which is at
least the length of the value it produces, so that the cost of a run bounds both
the number of oracle queries and the length of every query.  This is a faithful
cost model for polynomial time (it is a "for"-loop language with the standard
Cobham primitives).

`P^O` and `NP^O` are then defined in the usual way.
-/

namespace CS.BGS

/-- Bit strings. -/
abbrev Str := List Bool

/-- An oracle is a set of strings, presented as its characteristic function. -/
abbrev Oracle := Str → Bool

/-- Expressions of the machine language. -/
inductive Expr : Type
  | var (i : ℕ) : Expr
  | lit (s : Str) : Expr
  | cat (a b : Expr) : Expr
  /-- `smash a b` is the all-zero string of length `|a| * |b|`. -/
  | smash (a b : Expr) : Expr
  | tail (a : Expr) : Expr
  /-- `eqE a b` is `[true]` if the two values are equal, `[]` otherwise. -/
  | eqE (a b : Expr) : Expr
  /-- `query a` is `[true]` if the value of `a` is in the oracle, `[]` otherwise. -/
  | query (a : Expr) : Expr
  deriving DecidableEq

/-- Programs of the machine language. -/
inductive Prog : Type
  | skip : Prog
  | assign (i : ℕ) (e : Expr) : Prog
  | seq (a b : Prog) : Prog
  | ite (c : Expr) (t f : Prog) : Prog
  /-- `loop c body` runs `body` exactly `|c|` times (`c` is evaluated once, first). -/
  | loop (c : Expr) (body : Prog) : Prog
  deriving DecidableEq

/-- A machine state: the values of the variables, the cost incurred so far, and the
list of oracle queries made so far. -/
structure State where
  vars : ℕ → Str
  cost : ℕ
  qs : List Str

/-- Update a variable assignment. -/
def upd (v : ℕ → Str) (i : ℕ) (s : Str) : ℕ → Str := fun j => if j = i then s else v j

/-- Evaluation of expressions: returns the value and the new state. -/
def evalE (O : Oracle) : Expr → State → Str × State
  | .var i, st => (st.vars i, { st with cost := st.cost + 1 })
  | .lit s, st => (s, { st with cost := st.cost + s.length + 1 })
  | .cat a b, st =>
      let ra := evalE O a st
      let rb := evalE O b ra.2
      (ra.1 ++ rb.1, { rb.2 with cost := rb.2.cost + ra.1.length + rb.1.length + 1 })
  | .smash a b, st =>
      let ra := evalE O a st
      let rb := evalE O b ra.2
      (List.replicate (ra.1.length * rb.1.length) false,
        { rb.2 with cost := rb.2.cost + ra.1.length * rb.1.length + 1 })
  | .tail a, st =>
      let ra := evalE O a st
      (ra.1.tail, { ra.2 with cost := ra.2.cost + 1 })
  | .eqE a b, st =>
      let ra := evalE O a st
      let rb := evalE O b ra.2
      ((if ra.1 = rb.1 then [true] else []),
        { rb.2 with cost := rb.2.cost + ra.1.length + rb.1.length + 1 })
  | .query a, st =>
      let ra := evalE O a st
      ((if O ra.1 then [true] else []),
        { ra.2 with cost := ra.2.cost + ra.1.length + 1, qs := ra.1 :: ra.2.qs })

/-- Execution of programs. -/
def run (O : Oracle) : Prog → State → State
  | .skip, st => { st with cost := st.cost + 1 }
  | .assign i e, st =>
      let r := evalE O e st
      { r.2 with vars := upd r.2.vars i r.1, cost := r.2.cost + r.1.length + 1 }
  | .seq a b, st => run O b (run O a st)
  | .ite c t f, st =>
      let r := evalE O c st
      if r.1 = [] then run O f { r.2 with cost := r.2.cost + 1 }
      else run O t { r.2 with cost := r.2.cost + 1 }
  | .loop c body, st =>
      let r := evalE O c st
      (run O body)^[r.1.length] { r.2 with cost := r.2.cost + 1 }

/-- The initial state on input `x` and witness `w`. -/
def initSt (x w : Str) : State :=
  { vars := fun i => if i = 0 then x else if i = 1 then w else [], cost := 0, qs := [] }

/-- The machine accepts if variable `0` holds a nonempty string at the end. -/
def accepts (O : Oracle) (p : Prog) (x w : Str) : Prop :=
  (run O p (initSt x w)).vars 0 ≠ []

/-- The cost of running `p` on input `x` and witness `w`. -/
def cost (O : Oracle) (p : Prog) (x w : Str) : ℕ := (run O p (initSt x w)).cost

/-- `L ∈ P^O`: there is a program and an exponent `k` such that the program runs in
time `(|x|+2)^k` and decides `L` (the witness variable is initialised to `[]`). -/
def inP (O : Oracle) (L : Set Str) : Prop :=
  ∃ (p : Prog) (k : ℕ), (∀ x : Str, cost O p x [] ≤ (x.length + 2) ^ k) ∧
    (∀ x : Str, x ∈ L ↔ accepts O p x [])

/-- `L ∈ NP^O`: there is a verifier running in time `(|x|+2)^k` on all witnesses of
length at most `(|x|+2)^k`, accepting some such witness exactly for `x ∈ L`. -/
def inNP (O : Oracle) (L : Set Str) : Prop :=
  ∃ (p : Prog) (k : ℕ),
    (∀ x w : Str, w.length ≤ (x.length + 2) ^ k → cost O p x w ≤ (x.length + 2) ^ k) ∧
    (∀ x : Str, x ∈ L ↔ ∃ w : Str, w.length ≤ (x.length + 2) ^ k ∧ accepts O p x w)

/-- The class `P^O`. -/
def PClass (O : Oracle) : Set (Set Str) := {L | inP O L}

/-- The class `NP^O`. -/
def NPClass (O : Oracle) : Set (Set Str) := {L | inNP O L}

end CS.BGS

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

