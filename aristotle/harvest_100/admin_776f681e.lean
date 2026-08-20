/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is self-contained (no imports): it builds, from scratch,

* propositional formulas in conjunctive normal form (CNF) and satisfiability,
* Boolean circuits (as formulas over a fixed set of input variables),
* the Tseitin transformation from circuits to CNF, with its correctness proof
  and a linear size bound,
* the notion of an `NP` verifier (a polynomial-size circuit family together
  with a polynomially bounded witness length),

and proves the Cook–Levin theorem in the following form.

`Frontier.cook_levin`: every language `L` admitting a polynomial-size circuit
verifier reduces to `SAT` by an (explicitly constructed, hence computable)
map `f` such that `x ∈ L ↔ f x` is satisfiable, and the size of `f x` is
bounded by a polynomial in the length of `x`.

`Frontier.sat_in_np`: conversely, `SAT` itself lies in `NP`: a CNF `c` is
satisfiable iff there is a witness (a Boolean word of length the number of
variables of `c`) accepted by a circuit of size linear in `c`, which is
constructed from `c` by the explicit map `cnfCircuit`.

## Scope

Membership in `NP` is formalised here through *verifier circuits* rather than
through Turing machines: a language is in `NP` when there are a circuit family
`V` of polynomially bounded size and a witness-length function `m` such that
`V n` accepts exactly the pairs (input of length `n`, witness of length `m n`)
that certify membership. The step which is proved is therefore the
circuit-satisfiability core of Cook–Levin (the Tseitin translation of an
arbitrary verifier circuit into an equisatisfiable CNF of linear size, together
with the hard-wiring of the input), and not the simulation of a
polynomial-time Turing machine by a polynomial-size circuit family. All
constructions here are explicit computable functions, and the size bounds are
proved, not assumed.
-/

namespace Frontier

/-! ## Polynomial bounds -/

/-- A function `Nat → Nat` is polynomially bounded. The shifted base `n+1`
avoids degenerate behaviour at `n = 0`. -/
def IsPolyBound (g : Nat → Nat) : Prop := ∃ a b : Nat, ∀ n, g n ≤ a * (n + 1) ^ b

theorem isPolyBound_add {g h : Nat → Nat} (hg : IsPolyBound g) (hh : IsPolyBound h) :
    IsPolyBound (fun n => g n + h n) := by
  obtain ⟨a1, b1, h1⟩ := hg
  obtain ⟨a2, b2, h2⟩ := hh
  refine ⟨a1 + a2, max b1 b2, fun n => ?_⟩
  have e1 : (n + 1) ^ b1 ≤ (n + 1) ^ (max b1 b2) :=
    Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_max_left _ _)
  have e2 : (n + 1) ^ b2 ≤ (n + 1) ^ (max b1 b2) :=
    Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_max_right _ _)
  calc g n + h n ≤ a1 * (n + 1) ^ b1 + a2 * (n + 1) ^ b2 := Nat.add_le_add (h1 n) (h2 n)
    _ ≤ a1 * (n + 1) ^ (max b1 b2) + a2 * (n + 1) ^ (max b1 b2) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
    _ = (a1 + a2) * (n + 1) ^ (max b1 b2) := by rw [Nat.add_mul]

theorem isPolyBound_mul_const {g : Nat → Nat} (c : Nat) (hg : IsPolyBound g) :
    IsPolyBound (fun n => c * g n) := by
  obtain ⟨a, b, h⟩ := hg
  refine ⟨c * a, b, fun n => ?_⟩
  calc c * g n ≤ c * (a * (n + 1) ^ b) := Nat.mul_le_mul_left _ (h n)
    _ = c * a * (n + 1) ^ b := by rw [Nat.mul_assoc]

theorem isPolyBound_linear : IsPolyBound (fun n => n) :=
  ⟨1, 1, fun n => by simp⟩

theorem isPolyBound_const (c : Nat) : IsPolyBound (fun _ => c) :=
  ⟨c, 0, fun n => by simp⟩

theorem isPolyBound_mono {g h : Nat → Nat} (hg : IsPolyBound g) (hle : ∀ n, h n ≤ g n) :
    IsPolyBound h := by
  obtain ⟨a, b, hb⟩ := hg
  exact ⟨a, b, fun n => Nat.le_trans (hle n) (hb n)⟩

/-! ## CNF formulas -/

/-- A literal over the variable type `α`: a variable and a polarity. -/
abbrev Lit (α : Type) : Type := α × Bool
/-- A clause is a disjunction of literals. -/
abbrev Clause (α : Type) : Type := List (Lit α)
/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF (α : Type) : Type := List (Clause α)

/-- Negation of a literal. -/
def negLit {α : Type} (l : Lit α) : Lit α := (l.1, !l.2)

/-- Value of a literal under an assignment. -/
def litEval {α : Type} (σ : α → Bool) (l : Lit α) : Bool :=
  if l.2 then σ l.1 else !(σ l.1)

/-- Value of a CNF formula under an assignment. -/
def cnfEval {α : Type} (σ : α → Bool) (c : CNF α) : Bool :=
  c.all (fun cl => cl.any (litEval σ))

/-- Satisfiability of a CNF formula. -/
def Sat {α : Type} (c : CNF α) : Prop := ∃ σ : α → Bool, cnfEval σ c = true

/-- Size of a CNF formula: number of clauses plus total number of literals. -/
def cnfSize {α : Type} (c : CNF α) : Nat :=
  c.length + (c.map List.length).foldr (· + ·) 0

@[simp] theorem litEval_mk_true {α : Type} (σ : α → Bool) (v : α) :
    litEval σ (v, true) = σ v := rfl

@[simp] theorem litEval_mk_false {α : Type} (σ : α → Bool) (v : α) :
    litEval σ (v, false) = !σ v := rfl

theorem litEval_negLit {α : Type} (σ : α → Bool) (l : Lit α) :
    litEval σ (negLit l) = !(litEval σ l) := by
  cases l with
  | mk v b => cases b <;> simp [litEval, negLit]

theorem cnfEval_append {α : Type} (σ : α → Bool) (c d : CNF α) :
    cnfEval σ (c ++ d) = (cnfEval σ c && cnfEval σ d) := by
  simp [cnfEval]

theorem cnfEval_cons {α : Type} (σ : α → Bool) (cl : Clause α) (c : CNF α) :
    cnfEval σ (cl :: c) = (cl.any (litEval σ) && cnfEval σ c) := by
  simp [cnfEval]

theorem clause_any_congr {α : Type} {σ τ : α → Bool} {cl : Clause α}
    (h : ∀ l ∈ cl, σ l.1 = τ l.1) : cl.any (litEval σ) = cl.any (litEval τ) := by
  induction cl with
  | nil => rfl
  | cons l cl ih =>
    have h1 : litEval σ l = litEval τ l := by simp [litEval, h l (by simp)]
    simp only [List.any_cons, h1, ih (fun l' hl' => h l' (by simp [hl']))]

theorem cnfEval_congr {α : Type} {σ τ : α → Bool} {c : CNF α}
    (h : ∀ cl ∈ c, ∀ l ∈ cl, σ l.1 = τ l.1) : cnfEval σ c = cnfEval τ c := by
  induction c with
  | nil => rfl
  | cons cl c ih =>
    simp only [cnfEval, List.all_cons] at *
    rw [clause_any_congr (h cl (by simp)), ih (fun cl' hcl' => h cl' (by simp [hcl']))]

/-! ## Renaming variables -/

/-- Rename the variables of a CNF formula. -/
def cnfMap {α β : Type} (f : α → β) (c : CNF α) : CNF β :=
  c.map (fun cl => cl.map (fun l => (f l.1, l.2)))

theorem cnfEval_cnfMap {α β : Type} (f : α → β) (σ : β → Bool) (c : CNF α) :
    cnfEval σ (cnfMap f c) = cnfEval (fun a => σ (f a)) c := by
  induction c with
  | nil => rfl
  | cons cl c ih =>
    simp only [cnfMap, List.map_cons, cnfEval, List.all_cons] at *
    rw [ih]
    congr 1
    induction cl with
    | nil => rfl
    | cons l cl ih2 => simp only [List.map_cons, List.any_cons, ih2, litEval]

theorem cnfSize_cons {α : Type} (cl : Clause α) (c : CNF α) :
    cnfSize (cl :: c) = 1 + cl.length + cnfSize c := by
  simp only [cnfSize, List.length_cons, List.map_cons, List.foldr_cons]
  omega

theorem cnfSize_append {α : Type} (c d : CNF α) :
    cnfSize (c ++ d) = cnfSize c + cnfSize d := by
  induction c with
  | nil => simp [cnfSize]
  | cons cl c ih =>
    rw [List.cons_append, cnfSize_cons, cnfSize_cons, ih]
    omega

theorem cnfSize_cnfMap {α β : Type} (f : α → β) (c : CNF α) :
    cnfSize (cnfMap f c) = cnfSize c := by
  simp only [cnfSize, cnfMap, List.length_map, List.map_map]
  congr 1
  induction c with
  | nil => rfl
  | cons cl c ih => simp [ih]

open Classical in
/-- Pull an assignment back along an injective renaming. -/
noncomputable def pullbackAssign {α β : Type} (f : α → β) (σ : α → Bool) : β → Bool :=
  fun b => if h : ∃ a, f a = b then σ (Classical.choose h) else false

theorem pullbackAssign_apply {α β : Type} {f : α → β} (hf : Function.Injective f)
    (σ : α → Bool) (a : α) : pullbackAssign f σ (f a) = σ a := by
  have h : ∃ a', f a' = f a := ⟨a, rfl⟩
  have hc : f (Classical.choose h) = f a := Classical.choose_spec h
  simp only [pullbackAssign, dif_pos h]
  rw [hf hc]

theorem sat_cnfMap_iff {α β : Type} {f : α → β} (hf : Function.Injective f) (c : CNF α) :
    Sat (cnfMap f c) ↔ Sat c := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨fun a => σ (f a), by rw [← cnfEval_cnfMap]; exact hσ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨pullbackAssign f σ, ?_⟩
    rw [cnfEval_cnfMap]
    rw [show (fun a => pullbackAssign f σ (f a)) = σ from funext fun a =>
      pullbackAssign_apply hf σ a]
    exact hσ

/-! ## Boolean circuits -/

/-- Boolean circuits over the variables `Nat`. -/
inductive Circuit : Type
  | var (i : Nat) : Circuit
  | tru : Circuit
  | fls : Circuit
  | neg (a : Circuit) : Circuit
  | conj (a b : Circuit) : Circuit
  | disj (a b : Circuit) : Circuit
  deriving Repr

/-- Value of a circuit under an assignment of its variables. -/
def Circuit.eval (τ : Nat → Bool) : Circuit → Bool
  | .var i => τ i
  | .tru => true
  | .fls => false
  | .neg a => !(a.eval τ)
  | .conj a b => (a.eval τ && b.eval τ)
  | .disj a b => (a.eval τ || b.eval τ)

/-- Number of nodes of a circuit. -/
def Circuit.size : Circuit → Nat
  | .var _ => 1
  | .tru => 1
  | .fls => 1
  | .neg a => a.size + 1
  | .conj a b => a.size + b.size + 1
  | .disj a b => a.size + b.size + 1

/-- All variables of the circuit are `< n`. -/
def Circuit.VarsBelow : Circuit → Nat → Prop
  | .var i, n => i < n
  | .tru, _ => True
  | .fls, _ => True
  | .neg a, n => a.VarsBelow n
  | .conj a b, n => a.VarsBelow n ∧ b.VarsBelow n
  | .disj a b, n => a.VarsBelow n ∧ b.VarsBelow n

theorem Circuit.eval_congr {c : Circuit} {n : Nat} (hc : c.VarsBelow n)
    {τ₁ τ₂ : Nat → Bool} (h : ∀ i, i < n → τ₁ i = τ₂ i) : c.eval τ₁ = c.eval τ₂ := by
  induction c with
  | var i => exact h i hc
  | tru => rfl
  | fls => rfl
  | neg a ih => simp [Circuit.eval, ih hc]
  | conj a b iha ihb => simp [Circuit.eval, iha hc.1, ihb hc.2]
  | disj a b iha ihb => simp [Circuit.eval, iha hc.1, ihb hc.2]

/-! ## The Tseitin transformation -/

/-- Result of the Tseitin transformation: an output literal, a set of defining
clauses, and the next free gate-variable index. Variables of the resulting CNF
are `Sum.inl i` for the circuit variables `i` and `Sum.inr j` for gate variables. -/
structure TseitinResult : Type where
  /-- Literal representing the value of the circuit. -/
  out : Lit (Nat ⊕ Nat)
  /-- Defining clauses of the gates. -/
  cls : CNF (Nat ⊕ Nat)
  /-- The next unused gate variable index. -/
  next : Nat

/-- The Tseitin transformation of a circuit, using gate variables `Sum.inr j`
with `j ≥ k`. -/
def tseitin : Circuit → Nat → TseitinResult
  | .var i, k => ⟨(Sum.inl i, true), [], k⟩
  | .tru, k => ⟨(Sum.inr k, true), [[(Sum.inr k, true)]], k + 1⟩
  | .fls, k => ⟨(Sum.inr k, true), [[(Sum.inr k, false)]], k + 1⟩
  | .neg a, k =>
      let r := tseitin a k
      ⟨negLit r.out, r.cls, r.next⟩
  | .conj a b, k =>
      let ra := tseitin a k
      let rb := tseitin b ra.next
      let g : Lit (Nat ⊕ Nat) := (Sum.inr rb.next, true)
      ⟨g, [negLit g, ra.out] :: [negLit g, rb.out] :: [g, negLit ra.out, negLit rb.out] ::
        (ra.cls ++ rb.cls), rb.next + 1⟩
  | .disj a b, k =>
      let ra := tseitin a k
      let rb := tseitin b ra.next
      let g : Lit (Nat ⊕ Nat) := (Sum.inr rb.next, true)
      ⟨g, [negLit g, ra.out, rb.out] :: [g, negLit ra.out] :: [g, negLit rb.out] ::
        (ra.cls ++ rb.cls), rb.next + 1⟩

/-- All gate variables occurring in `c` have index in `[lo, hi)`. -/
def VarsIn (c : CNF (Nat ⊕ Nat)) (lo hi : Nat) : Prop :=
  ∀ cl ∈ c, ∀ l ∈ cl, ∀ j, l.1 = Sum.inr j → lo ≤ j ∧ j < hi

theorem tseitin_next_ge (c : Circuit) : ∀ k : Nat, k ≤ (tseitin c k).next := by
  induction c with
  | var i => intro k; simp [tseitin]
  | tru => intro k; simp [tseitin]
  | fls => intro k; simp [tseitin]
  | neg a ih => intro k; simpa [tseitin] using ih k
  | conj a b iha ihb =>
      intro k
      have h1 := iha k
      have h2 := ihb (tseitin a k).next
      simp only [tseitin]
      omega
  | disj a b iha ihb =>
      intro k
      have h1 := iha k
      have h2 := ihb (tseitin a k).next
      simp only [tseitin]
      omega

theorem tseitin_out_var (c : Circuit) : ∀ (k j : Nat),
    (tseitin c k).out.1 = Sum.inr j → k ≤ j ∧ j < (tseitin c k).next := by
  induction c with
  | var i => intro k j h; simp [tseitin] at h
  | tru => intro k j h; simp only [tseitin, Sum.inr.injEq] at h ⊢; omega
  | fls => intro k j h; simp only [tseitin, Sum.inr.injEq] at h ⊢; omega
  | neg a ih =>
      intro k j h
      simp only [tseitin, negLit] at h ⊢
      exact ih k j h
  | conj a b iha ihb =>
      intro k j h
      have h1 := tseitin_next_ge a k
      have h2 := tseitin_next_ge b (tseitin a k).next
      simp only [tseitin, Sum.inr.injEq] at h ⊢
      omega
  | disj a b iha ihb =>
      intro k j h
      have h1 := tseitin_next_ge a k
      have h2 := tseitin_next_ge b (tseitin a k).next
      simp only [tseitin, Sum.inr.injEq] at h ⊢
      omega

theorem tseitin_vars (c : Circuit) : ∀ k : Nat,
    VarsIn (tseitin c k).cls k (tseitin c k).next := by
  induction c with
  | var i => intro k cl hcl; simp [tseitin] at hcl
  | tru =>
      intro k cl hcl l hl j hj
      simp only [tseitin, List.mem_cons, List.not_mem_nil, or_false] at hcl hl ⊢
      subst hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simp only [Sum.inr.injEq] at hj
      omega
  | fls =>
      intro k cl hcl l hl j hj
      simp only [tseitin, List.mem_cons, List.not_mem_nil, or_false] at hcl hl ⊢
      subst hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simp only [Sum.inr.injEq] at hj
      omega
  | neg a ih =>
      intro k cl hcl l hl j hj
      simp only [tseitin] at hcl ⊢
      exact ih k cl hcl l hl j hj
  | conj a b iha ihb =>
      intro k cl hcl l hl j hj
      have hva := iha k
      have hvb := ihb (tseitin a k).next
      have h1 := tseitin_next_ge a k
      have h2 := tseitin_next_ge b (tseitin a k).next
      have hoa := tseitin_out_var a k j
      have hob := tseitin_out_var b (tseitin a k).next j
      simp only [tseitin, List.mem_cons, List.mem_append] at hcl ⊢
      rcases hcl with rfl | rfl | rfl | hcl | hcl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · simp only [negLit, Sum.inr.injEq] at hj; omega
        · have := hoa hj; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · simp only [negLit, Sum.inr.injEq] at hj; omega
        · have := hob hj; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · simp only [Sum.inr.injEq] at hj; omega
        · have := hoa (by simpa [negLit] using hj); omega
        · have := hob (by simpa [negLit] using hj); omega
      · have := hva cl hcl l hl j hj; omega
      · have := hvb cl hcl l hl j hj; omega
  | disj a b iha ihb =>
      intro k cl hcl l hl j hj
      have hva := iha k
      have hvb := ihb (tseitin a k).next
      have h1 := tseitin_next_ge a k
      have h2 := tseitin_next_ge b (tseitin a k).next
      have hoa := tseitin_out_var a k j
      have hob := tseitin_out_var b (tseitin a k).next j
      simp only [tseitin, List.mem_cons, List.mem_append] at hcl ⊢
      rcases hcl with rfl | rfl | rfl | hcl | hcl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · simp only [negLit, Sum.inr.injEq] at hj; omega
        · have := hoa hj; omega
        · have := hob hj; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · simp only [Sum.inr.injEq] at hj; omega
        · have := hoa (by simpa [negLit] using hj); omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · simp only [Sum.inr.injEq] at hj; omega
        · have := hob (by simpa [negLit] using hj); omega
      · have := hva cl hcl l hl j hj; omega
      · have := hvb cl hcl l hl j hj; omega

theorem tseitin_sound (c : Circuit) : ∀ (k : Nat) (σ : Nat ⊕ Nat → Bool),
    cnfEval σ (tseitin c k).cls = true →
    litEval σ (tseitin c k).out = c.eval (fun i => σ (Sum.inl i)) := by
  induction c with
  | var i => intro k σ _; simp [tseitin, Circuit.eval]
  | tru =>
      intro k σ h
      simp only [tseitin, cnfEval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
        Bool.or_false, litEval_mk_true, Bool.and_true] at h
      simp [tseitin, Circuit.eval, h]
  | fls =>
      intro k σ h
      simp only [tseitin, cnfEval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
        Bool.or_false, litEval_mk_false, Bool.and_true, Bool.not_eq_eq_eq_not,
        Bool.not_true] at h
      simp [tseitin, Circuit.eval, h]
  | neg a ih =>
      intro k σ h
      simp only [tseitin] at h ⊢
      rw [litEval_negLit, ih k σ h]
      rfl
  | conj a b iha ihb =>
      intro k σ h
      simp only [tseitin, cnfEval, List.all_cons, List.all_append, List.any_cons, List.any_nil,
        Bool.or_false, Bool.and_eq_true, litEval_negLit, litEval_mk_true] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have ea := iha k σ h4
      have eb := ihb (tseitin a k).next σ h5
      simp only [tseitin, Circuit.eval, litEval_mk_true, ← ea, ← eb]
      revert h1 h2 h3
      generalize σ (Sum.inr (tseitin b (tseitin a k).next).next) = G
      generalize litEval σ (tseitin a k).out = A
      generalize litEval σ (tseitin b (tseitin a k).next).out = B
      revert A B G
      decide
  | disj a b iha ihb =>
      intro k σ h
      simp only [tseitin, cnfEval, List.all_cons, List.all_append, List.any_cons, List.any_nil,
        Bool.or_false, Bool.and_eq_true, litEval_negLit, litEval_mk_true] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have ea := iha k σ h4
      have eb := ihb (tseitin a k).next σ h5
      simp only [tseitin, Circuit.eval, litEval_mk_true, ← ea, ← eb]
      revert h1 h2 h3
      generalize σ (Sum.inr (tseitin b (tseitin a k).next).next) = G
      generalize litEval σ (tseitin a k).out = A
      generalize litEval σ (tseitin b (tseitin a k).next).out = B
      revert A B G
      decide

/-- Update an assignment at a single gate variable. -/
def updAt (σ : Nat ⊕ Nat → Bool) (j₀ : Nat) (v : Bool) : Nat ⊕ Nat → Bool := fun w =>
  match w with
  | Sum.inl i => σ (Sum.inl i)
  | Sum.inr j => if j = j₀ then v else σ (Sum.inr j)

@[simp] theorem updAt_inl (σ : Nat ⊕ Nat → Bool) (j₀ : Nat) (v : Bool) (i : Nat) :
    updAt σ j₀ v (Sum.inl i) = σ (Sum.inl i) := rfl

@[simp] theorem updAt_inr_self (σ : Nat ⊕ Nat → Bool) (j₀ : Nat) (v : Bool) :
    updAt σ j₀ v (Sum.inr j₀) = v := by simp [updAt]

theorem updAt_inr_ne (σ : Nat ⊕ Nat → Bool) {j j₀ : Nat} (v : Bool) (h : j ≠ j₀) :
    updAt σ j₀ v (Sum.inr j) = σ (Sum.inr j) := by simp [updAt, h]

theorem litEval_congr {α : Type} {σ τ : α → Bool} {l : Lit α} (h : σ l.1 = τ l.1) :
    litEval σ l = litEval τ l := by simp [litEval, h]

theorem cnfEval_congr_vars {cls : CNF (Nat ⊕ Nat)} {lo hi : Nat} (hv : VarsIn cls lo hi)
    {σ τ : Nat ⊕ Nat → Bool} (hinl : ∀ i, σ (Sum.inl i) = τ (Sum.inl i))
    (hinr : ∀ j, lo ≤ j → j < hi → σ (Sum.inr j) = τ (Sum.inr j)) :
    cnfEval σ cls = cnfEval τ cls := by
  refine cnfEval_congr (fun cl hcl l hl => ?_)
  cases hvar : l.1 with
  | inl i => exact hinl i
  | inr j =>
    obtain ⟨hlo, hhi⟩ := hv cl hcl l hl j hvar
    exact hinr j hlo hhi

theorem litEval_out_congr (a : Circuit) (k : Nat) {σ τ : Nat ⊕ Nat → Bool}
    (hinl : ∀ i, σ (Sum.inl i) = τ (Sum.inl i))
    (hinr : ∀ j, k ≤ j → j < (tseitin a k).next → σ (Sum.inr j) = τ (Sum.inr j)) :
    litEval σ (tseitin a k).out = litEval τ (tseitin a k).out := by
  refine litEval_congr ?_
  cases hvar : (tseitin a k).out.1 with
  | inl i => exact hinl i
  | inr j =>
    obtain ⟨hlo, hhi⟩ := tseitin_out_var a k j hvar
    exact hinr j hlo hhi

theorem tseitin_complete (c : Circuit) : ∀ (k : Nat) (τ : Nat → Bool) (σ₀ : Nat ⊕ Nat → Bool),
    (∀ i, σ₀ (Sum.inl i) = τ i) →
    ∃ σ : Nat ⊕ Nat → Bool,
      (∀ i, σ (Sum.inl i) = τ i) ∧
      (∀ j, (j < k ∨ (tseitin c k).next ≤ j) → σ (Sum.inr j) = σ₀ (Sum.inr j)) ∧
      cnfEval σ (tseitin c k).cls = true ∧
      litEval σ (tseitin c k).out = c.eval τ := by
  induction c with
  | var i =>
      intro k τ σ₀ h₀
      exact ⟨σ₀, h₀, fun j _ => rfl, by simp [tseitin, cnfEval],
        by simp [tseitin, Circuit.eval, h₀]⟩
  | tru =>
      intro k τ σ₀ h₀
      refine ⟨updAt σ₀ k true, fun i => h₀ i, ?_, ?_, ?_⟩
      · intro j hj
        simp only [tseitin] at hj
        exact updAt_inr_ne _ _ (by omega)
      · simp [tseitin, cnfEval]
      · simp [tseitin, Circuit.eval]
  | fls =>
      intro k τ σ₀ h₀
      refine ⟨updAt σ₀ k false, fun i => h₀ i, ?_, ?_, ?_⟩
      · intro j hj
        simp only [tseitin] at hj
        exact updAt_inr_ne _ _ (by omega)
      · simp [tseitin, cnfEval]
      · simp [tseitin, Circuit.eval]
  | neg a ih =>
      intro k τ σ₀ h₀
      obtain ⟨σ, hl, hr, hc, ho⟩ := ih k τ σ₀ h₀
      refine ⟨σ, hl, ?_, ?_, ?_⟩
      · simpa only [tseitin] using hr
      · simpa only [tseitin] using hc
      · simp only [tseitin, litEval_negLit, ho, Circuit.eval]
  | conj a b iha ihb =>
      intro k τ σ₀ h₀
      obtain ⟨σ1, h1l, h1r, h1c, h1o⟩ := iha k τ σ₀ h₀
      obtain ⟨σ2, h2l, h2r, h2c, h2o⟩ := ihb (tseitin a k).next τ σ1 h1l
      have hk1 := tseitin_next_ge a k
      have hk2 := tseitin_next_ge b (tseitin a k).next
      have hinl1 : ∀ i, updAt σ2 (tseitin b (tseitin a k).next).next
          (a.eval τ && b.eval τ) (Sum.inl i) = σ1 (Sum.inl i) := by
        intro i; rw [updAt_inl, h2l i, ← h1l i]
      have hinl2 : ∀ i, updAt σ2 (tseitin b (tseitin a k).next).next
          (a.eval τ && b.eval τ) (Sum.inl i) = σ2 (Sum.inl i) := fun _ => rfl
      have hAgreeA : ∀ j, k ≤ j → j < (tseitin a k).next →
          updAt σ2 (tseitin b (tseitin a k).next).next
            (a.eval τ && b.eval τ) (Sum.inr j) = σ1 (Sum.inr j) := by
        intro j hlo hhi
        rw [updAt_inr_ne _ _ (by omega)]
        exact h2r j (Or.inl (by omega))
      have hAgreeB : ∀ j, (tseitin a k).next ≤ j → j < (tseitin b (tseitin a k).next).next →
          updAt σ2 (tseitin b (tseitin a k).next).next
            (a.eval τ && b.eval τ) (Sum.inr j) = σ2 (Sum.inr j) := by
        intro j _ hhi
        exact updAt_inr_ne _ _ (by omega)
      refine ⟨updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ && b.eval τ),
        fun i => h2l i, ?_, ?_, ?_⟩
      · intro j hj
        simp only [tseitin] at hj
        rw [updAt_inr_ne _ _ (by omega), h2r j (by omega)]
        exact h1r j (by omega)
      · have ea : litEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ && b.eval τ))
            (tseitin a k).out = a.eval τ := by
          rw [litEval_out_congr a k hinl1 hAgreeA]; exact h1o
        have eb : litEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ && b.eval τ))
            (tseitin b (tseitin a k).next).out = b.eval τ := by
          rw [litEval_out_congr b _ hinl2 hAgreeB]; exact h2o
        have ca : cnfEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ && b.eval τ))
            (tseitin a k).cls = true := by
          rw [cnfEval_congr_vars (tseitin_vars a k) hinl1 hAgreeA]; exact h1c
        have cb : cnfEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ && b.eval τ))
            (tseitin b (tseitin a k).next).cls = true := by
          rw [cnfEval_congr_vars (tseitin_vars b _) hinl2 hAgreeB]; exact h2c
        simp only [tseitin, cnfEval, List.all_cons, List.all_append, List.any_cons, List.any_nil,
          Bool.or_false, Bool.and_eq_true, litEval_negLit, litEval_mk_true, updAt_inr_self, ea, eb]
        refine ⟨?_, ?_, ?_, ca, cb⟩ <;>
          cases hA : a.eval τ <;> cases hB : b.eval τ <;> rfl
      · simp [tseitin, Circuit.eval]
  | disj a b iha ihb =>
      intro k τ σ₀ h₀
      obtain ⟨σ1, h1l, h1r, h1c, h1o⟩ := iha k τ σ₀ h₀
      obtain ⟨σ2, h2l, h2r, h2c, h2o⟩ := ihb (tseitin a k).next τ σ1 h1l
      have hk1 := tseitin_next_ge a k
      have hk2 := tseitin_next_ge b (tseitin a k).next
      have hinl1 : ∀ i, updAt σ2 (tseitin b (tseitin a k).next).next
          (a.eval τ || b.eval τ) (Sum.inl i) = σ1 (Sum.inl i) := by
        intro i; rw [updAt_inl, h2l i, ← h1l i]
      have hinl2 : ∀ i, updAt σ2 (tseitin b (tseitin a k).next).next
          (a.eval τ || b.eval τ) (Sum.inl i) = σ2 (Sum.inl i) := fun _ => rfl
      have hAgreeA : ∀ j, k ≤ j → j < (tseitin a k).next →
          updAt σ2 (tseitin b (tseitin a k).next).next
            (a.eval τ || b.eval τ) (Sum.inr j) = σ1 (Sum.inr j) := by
        intro j hlo hhi
        rw [updAt_inr_ne _ _ (by omega)]
        exact h2r j (Or.inl (by omega))
      have hAgreeB : ∀ j, (tseitin a k).next ≤ j → j < (tseitin b (tseitin a k).next).next →
          updAt σ2 (tseitin b (tseitin a k).next).next
            (a.eval τ || b.eval τ) (Sum.inr j) = σ2 (Sum.inr j) := by
        intro j _ hhi
        exact updAt_inr_ne _ _ (by omega)
      refine ⟨updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ || b.eval τ),
        fun i => h2l i, ?_, ?_, ?_⟩
      · intro j hj
        simp only [tseitin] at hj
        rw [updAt_inr_ne _ _ (by omega), h2r j (by omega)]
        exact h1r j (by omega)
      · have ea : litEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ || b.eval τ))
            (tseitin a k).out = a.eval τ := by
          rw [litEval_out_congr a k hinl1 hAgreeA]; exact h1o
        have eb : litEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ || b.eval τ))
            (tseitin b (tseitin a k).next).out = b.eval τ := by
          rw [litEval_out_congr b _ hinl2 hAgreeB]; exact h2o
        have ca : cnfEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ || b.eval τ))
            (tseitin a k).cls = true := by
          rw [cnfEval_congr_vars (tseitin_vars a k) hinl1 hAgreeA]; exact h1c
        have cb : cnfEval (updAt σ2 (tseitin b (tseitin a k).next).next (a.eval τ || b.eval τ))
            (tseitin b (tseitin a k).next).cls = true := by
          rw [cnfEval_congr_vars (tseitin_vars b _) hinl2 hAgreeB]; exact h2c
        simp only [tseitin, cnfEval, List.all_cons, List.all_append, List.any_cons, List.any_nil,
          Bool.or_false, Bool.and_eq_true, litEval_negLit, litEval_mk_true, updAt_inr_self, ea, eb]
        refine ⟨?_, ?_, ?_, ca, cb⟩ <;>
          cases hA : a.eval τ <;> cases hB : b.eval τ <;> rfl
      · simp [tseitin, Circuit.eval]

theorem tseitin_size (c : Circuit) : ∀ k : Nat, cnfSize (tseitin c k).cls ≤ 10 * c.size := by
  induction c with
  | var i => intro k; simp [tseitin, cnfSize]
  | tru => intro k; simp [tseitin, cnfSize, Circuit.size]
  | fls => intro k; simp [tseitin, cnfSize, Circuit.size]
  | neg a ih =>
      intro k
      have := ih k
      simp only [tseitin, Circuit.size]
      omega
  | conj a b iha ihb =>
      intro k
      have h1 := iha k
      have h2 := ihb (tseitin a k).next
      simp only [tseitin, Circuit.size, cnfSize_cons, cnfSize_append, List.length_cons,
        List.length_nil]
      omega
  | disj a b iha ihb =>
      intro k
      have h1 := iha k
      have h2 := ihb (tseitin a k).next
      simp only [tseitin, Circuit.size, cnfSize_cons, cnfSize_append, List.length_cons,
        List.length_nil]
      omega

/-! ## The reduction -/

/-- Unit clauses forcing the input variables to the bits of `x`. -/
def inputClauses (x : List Bool) : CNF (Nat ⊕ Nat) :=
  (List.range x.length).map (fun i => [(Sum.inl i, x.getD i false)])

/-- Injection of the two kinds of variables into `Nat`. -/
def sumEnc : Nat ⊕ Nat → Nat := Sum.elim (fun i => 2 * i) (fun j => 2 * j + 1)

theorem sumEnc_injective : Function.Injective sumEnc := by
  rintro (a | a) (b | b) h <;> simp only [sumEnc, Sum.elim_inl, Sum.elim_inr] at h <;>
    simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] <;> omega

/-- The Cook–Levin reduction: from an input word `x` to a CNF formula which is
satisfiable exactly when the verifier circuit accepts `x` with some witness. -/
def reduction (V : Nat → Circuit) (x : List Bool) : CNF Nat :=
  let r := tseitin (V x.length) 0
  cnfMap sumEnc (r.cls ++ inputClauses x ++ [[r.out]])

theorem litEval_eq_true_iff {α : Type} (σ : α → Bool) (v : α) (b : Bool) :
    litEval σ (v, b) = true ↔ σ v = b := by
  cases b <;> simp [litEval]

theorem cnfEval_inputClauses_iff (σ : Nat ⊕ Nat → Bool) (x : List Bool) :
    cnfEval σ (inputClauses x) = true ↔
      ∀ i, i < x.length → σ (Sum.inl i) = x.getD i false := by
  simp only [cnfEval, inputClauses, List.all_eq_true, List.mem_map, List.mem_range]
  constructor
  · intro h i hi
    simpa [litEval_eq_true_iff] using h _ ⟨i, hi, rfl⟩
  · rintro h cl ⟨i, hi, rfl⟩
    simpa [litEval_eq_true_iff] using h i hi

theorem getD_append_left (x w : List Bool) (i : Nat) (h : i < x.length) :
    (x ++ w).getD i false = x.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, h]

theorem getD_append_right (x w : List Bool) (i : Nat) (h : x.length ≤ i) :
    (x ++ w).getD i false = w.getD (i - x.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, h]

theorem reduction_correct (V : Nat → Circuit) (m : Nat → Nat)
    (hvars : ∀ n, (V n).VarsBelow (n + m n)) (x : List Bool) :
    Sat (reduction V x) ↔
      ∃ w : List Bool, w.length = m x.length ∧
        (V x.length).eval (fun i => (x ++ w).getD i false) = true := by
  rw [reduction, sat_cnfMap_iff sumEnc_injective]
  constructor
  · rintro ⟨σ, hσ⟩
    rw [cnfEval_append, cnfEval_append, Bool.and_eq_true, Bool.and_eq_true] at hσ
    obtain ⟨⟨hcls, hin⟩, hout⟩ := hσ
    have hsound := tseitin_sound (V x.length) 0 σ hcls
    have houttrue : litEval σ (tseitin (V x.length) 0).out = true := by
      simpa [cnfEval] using hout
    have hev : (V x.length).eval (fun i => σ (Sum.inl i)) = true := by
      rw [← hsound]; exact houttrue
    have hinput := (cnfEval_inputClauses_iff σ x).1 hin
    refine ⟨(List.range (m x.length)).map (fun j => σ (Sum.inl (x.length + j))), by simp, ?_⟩
    rw [Circuit.eval_congr (hvars x.length) (τ₂ := fun i => σ (Sum.inl i)) ?_]
    · exact hev
    · intro i hi
      by_cases hlt : i < x.length
      · rw [getD_append_left _ _ _ hlt]
        exact (hinput i hlt).symm
      · have hge : x.length ≤ i := by omega
        rw [getD_append_right _ _ _ hge]
        have hidx : i - x.length < m x.length := by omega
        rw [List.getD_eq_getElem?_getD]
        simp only [List.getElem?_map, List.getElem?_range, hidx, Option.map_some,
          Option.getD_some]
        congr 2
        omega
  · rintro ⟨w, hwlen, hw⟩
    obtain ⟨σ, hl, -, hc, ho⟩ := tseitin_complete (V x.length) 0
      (fun i => (x ++ w).getD i false)
      (Sum.elim (fun i => (x ++ w).getD i false) (fun _ => false)) (fun _ => rfl)
    refine ⟨σ, ?_⟩
    rw [cnfEval_append, cnfEval_append, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨hc, ?_⟩, ?_⟩
    · rw [cnfEval_inputClauses_iff]
      intro i hi
      rw [hl i, getD_append_left _ _ _ hi]
    · simp only [cnfEval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
        Bool.or_false, Bool.and_true]
      rw [ho, hw]

theorem cnfSize_map_range (n : Nat) (f : Nat → Lit (Nat ⊕ Nat)) :
    cnfSize ((List.range n).map (fun i => [f i])) = 2 * n := by
  induction n with
  | zero => simp [cnfSize]
  | succ n ih =>
    have hlast : cnfSize [[f n]] = 2 := by simp [cnfSize]
    rw [List.range_succ, List.map_append, cnfSize_append, ih]
    simp only [List.map_cons, List.map_nil, hlast]
    omega

theorem cnfSize_inputClauses (x : List Bool) : cnfSize (inputClauses x) = 2 * x.length :=
  cnfSize_map_range _ _

theorem reduction_size (V : Nat → Circuit) (x : List Bool) :
    cnfSize (reduction V x) ≤ 10 * (V x.length).size + 2 * x.length + 2 := by
  have hts := tseitin_size (V x.length) 0
  have hlast : cnfSize [[(tseitin (V x.length) 0).out]] = 2 := by simp [cnfSize]
  simp only [reduction, cnfSize_cnfMap, cnfSize_append, cnfSize_inputClauses, hlast]
  omega

/-! ## Cook–Levin -/

/--
**Cook–Levin theorem** (NP-hardness of SAT).

Let `L` be a language of Boolean words which is verified by a family of Boolean
circuits `V` of polynomially bounded size, with polynomially bounded witness
length `m`: `x ∈ L` iff there is a witness `w` of length `m |x|` such that the
circuit `V |x|`, evaluated on the input bits of `x` followed by the bits of `w`,
outputs `true`.

Then `L` reduces to `SAT`: there is a map `f` from words to CNF formulas,
explicitly constructed (hence computable relative to `V`), such that `x ∈ L`
iff `f x` is satisfiable, and the size of `f x` is polynomially bounded in the
length of `x`.
-/
theorem cook_levin
    (L : List Bool → Prop) (V : Nat → Circuit) (m : Nat → Nat)
    (hvars : ∀ n, (V n).VarsBelow (n + m n))
    (hsize : IsPolyBound (fun n => (V n).size))
    (hV : ∀ x : List Bool, L x ↔ ∃ w : List Bool, w.length = m x.length ∧
        (V x.length).eval (fun i => (x ++ w).getD i false) = true) :
    ∃ (f : List Bool → CNF Nat) (g : Nat → Nat),
      (∀ x, L x ↔ Sat (f x)) ∧ IsPolyBound g ∧ ∀ x, cnfSize (f x) ≤ g x.length := by
  refine ⟨reduction V, fun n => 10 * (V n).size + 2 * n + 2, fun x => ?_, ?_,
    fun x => reduction_size V x⟩
  · rw [hV x, reduction_correct V m hvars x]
  · exact isPolyBound_add (isPolyBound_add (isPolyBound_mul_const 10 hsize)
      (isPolyBound_mul_const 2 isPolyBound_linear)) (isPolyBound_const 2)

/-! ## SAT belongs to NP -/

/-- The circuit computing the value of a literal. -/
def litCircuit (l : Lit Nat) : Circuit :=
  if l.2 then Circuit.var l.1 else Circuit.neg (Circuit.var l.1)

/-- The circuit computing the value of a clause. -/
def clauseCircuit : Clause Nat → Circuit
  | [] => Circuit.fls
  | l :: cl => Circuit.disj (litCircuit l) (clauseCircuit cl)

/-- The circuit computing the value of a CNF formula. -/
def cnfCircuit : CNF Nat → Circuit
  | [] => Circuit.tru
  | cl :: c => Circuit.conj (clauseCircuit cl) (cnfCircuit c)

theorem litCircuit_eval (σ : Nat → Bool) (l : Lit Nat) :
    (litCircuit l).eval σ = litEval σ l := by
  cases l with
  | mk v b => cases b <;> simp [litCircuit, litEval, Circuit.eval]

theorem clauseCircuit_eval (σ : Nat → Bool) (cl : Clause Nat) :
    (clauseCircuit cl).eval σ = cl.any (litEval σ) := by
  induction cl with
  | nil => rfl
  | cons l cl ih => simp [clauseCircuit, Circuit.eval, litCircuit_eval, ih]

theorem cnfCircuit_eval (σ : Nat → Bool) (c : CNF Nat) :
    (cnfCircuit c).eval σ = cnfEval σ c := by
  induction c with
  | nil => rfl
  | cons cl c ih => simp [cnfCircuit, Circuit.eval, clauseCircuit_eval, cnfEval, ih]

/-- The number of variables of a clause (one more than the largest index used). -/
def clauseNumVars (cl : Clause Nat) : Nat := cl.foldr (fun l a => max (l.1 + 1) a) 0

/-- The number of variables of a CNF formula (one more than the largest index used). -/
def cnfNumVars (c : CNF Nat) : Nat := c.foldr (fun cl a => max (clauseNumVars cl) a) 0

theorem Circuit.varsBelow_mono {c : Circuit} {n n' : Nat} (h : c.VarsBelow n) (hle : n ≤ n') :
    c.VarsBelow n' := by
  induction c with
  | var i => exact Nat.lt_of_lt_of_le h hle
  | tru => trivial
  | fls => trivial
  | neg a ih => exact ih h
  | conj a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | disj a b iha ihb => exact ⟨iha h.1, ihb h.2⟩

theorem clauseCircuit_varsBelow (cl : Clause Nat) :
    (clauseCircuit cl).VarsBelow (clauseNumVars cl) := by
  induction cl with
  | nil => trivial
  | cons l cl ih =>
    have h1 : l.1 + 1 ≤ clauseNumVars (l :: cl) := by
      simp only [clauseNumVars, List.foldr_cons]
      exact Nat.le_max_left _ _
    have h2 : clauseNumVars cl ≤ clauseNumVars (l :: cl) := by
      simp only [clauseNumVars, List.foldr_cons]
      exact Nat.le_max_right _ _
    refine ⟨?_, Circuit.varsBelow_mono ih h2⟩
    cases l with
    | mk v b =>
      cases b <;> exact (by simpa [litCircuit, Circuit.VarsBelow] using h1)

theorem cnfCircuit_varsBelow (c : CNF Nat) : (cnfCircuit c).VarsBelow (cnfNumVars c) := by
  induction c with
  | nil => trivial
  | cons cl c ih =>
    have h1 : clauseNumVars cl ≤ cnfNumVars (cl :: c) := by
      simp only [cnfNumVars, List.foldr_cons]
      exact Nat.le_max_left _ _
    have h2 : cnfNumVars c ≤ cnfNumVars (cl :: c) := by
      simp only [cnfNumVars, List.foldr_cons]
      exact Nat.le_max_right _ _
    exact ⟨Circuit.varsBelow_mono (clauseCircuit_varsBelow cl) h1, Circuit.varsBelow_mono ih h2⟩

theorem clauseCircuit_size (cl : Clause Nat) :
    (clauseCircuit cl).size ≤ 3 * cl.length + 1 := by
  induction cl with
  | nil => simp [clauseCircuit, Circuit.size]
  | cons l cl ih =>
    have hl : (litCircuit l).size ≤ 2 := by
      cases l with
      | mk v b => cases b <;> simp [litCircuit, Circuit.size]
    simp only [clauseCircuit, Circuit.size, List.length_cons]
    omega

/-- The verifier circuit for `SAT` has size linear in the size of the instance. -/
theorem cnfCircuit_size (c : CNF Nat) : (cnfCircuit c).size ≤ 3 * cnfSize c + 1 := by
  induction c with
  | nil => simp [cnfCircuit, Circuit.size, cnfSize]
  | cons cl c ih =>
    have h := clauseCircuit_size cl
    have hs : cnfSize (cl :: c) = 1 + cl.length + cnfSize c := cnfSize_cons cl c
    simp only [cnfCircuit, Circuit.size]
    omega

/--
`SAT` belongs to `NP`: a CNF formula `c` is satisfiable if and only if there is a
witness `w` (a Boolean word whose length is the number of variables of `c`)
accepted by the circuit `cnfCircuit c`, which is constructed from `c` and has
size linear in the size of `c` (see `Frontier.cnfCircuit_size`).
-/
theorem sat_in_np (c : CNF Nat) :
    Sat c ↔ ∃ w : List Bool, w.length = cnfNumVars c ∧
      (cnfCircuit c).eval (fun i => w.getD i false) = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨(List.range (cnfNumVars c)).map σ, by simp, ?_⟩
    rw [Circuit.eval_congr (cnfCircuit_varsBelow c) (τ₂ := σ) ?_, cnfCircuit_eval]
    · exact hσ
    · intro i hi
      simp [List.getD_eq_getElem?_getD, hi]
  · rintro ⟨w, -, hw⟩
    exact ⟨fun i => w.getD i false, by rw [← cnfCircuit_eval]; exact hw⟩

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

