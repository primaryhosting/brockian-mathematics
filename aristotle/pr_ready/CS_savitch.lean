/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace CS

/-! ## Machine model

We work with a *non-uniform* space-bounded machine model.  A machine works on inputs of one
fixed length; a language belongs to a space class if for every input length there is a machine
of the appropriate size deciding the language on inputs of that length.

A machine is described by its set of configurations `Cfg` (which is the whole memory of the
machine: the space used is `log₂ (card Cfg)`), a designated start configuration, a function
`head` telling which position of the (read-only) input is currently scanned, and a transition
which may depend on the current configuration and on the single input bit that is being read.
Note that the machine has *no* other access to the input, which is what makes the space measure
meaningful. -/

/-- The `i`-th bit of an input word; `false` beyond the end of the word. -/
def bitAt (x : List Bool) (i : ℕ) : Bool := x.getD i false

/-- A nondeterministic machine with configuration set `Cfg`. -/
structure NSM where
  /-- The set of configurations (the entire memory of the machine). -/
  Cfg : Type
  /-- The configuration set is finite. -/
  fintypeCfg : Fintype Cfg
  /-- Configurations can be compared. -/
  decEqCfg : DecidableEq Cfg
  /-- The initial configuration. -/
  start : Cfg
  /-- The accepting configurations. -/
  acc : Cfg → Bool
  /-- Position of the input head in a given configuration. -/
  head : Cfg → ℕ
  /-- `step a t b` says that `b` is a legal successor of `a` when the scanned input bit is `t`. -/
  step : Cfg → Bool → Cfg → Bool

attribute [instance] NSM.fintypeCfg NSM.decEqCfg

/-- The configuration graph of a nondeterministic machine on the input `x`. -/
def NSM.Edge (M : NSM) (x : List Bool) (a b : M.Cfg) : Prop :=
  M.step a (bitAt x (M.head a)) b = true

/-- A nondeterministic machine accepts `x` if some accepting configuration is reachable. -/
def NSM.Accepts (M : NSM) (x : List Bool) : Prop :=
  ∃ c, M.acc c = true ∧ Relation.ReflTransGen (M.Edge x) M.start c

/-- A deterministic machine with configuration set `Cfg`.  The field `out` marks the halting
configurations together with the answer they produce; halting is required to be permanent. -/
structure DSM where
  /-- The set of configurations (the entire memory of the machine). -/
  Cfg : Type
  /-- The configuration set is finite. -/
  fintypeCfg : Fintype Cfg
  /-- The initial configuration. -/
  start : Cfg
  /-- Position of the input head in a given configuration. -/
  head : Cfg → ℕ
  /-- The (deterministic) transition function, depending on the scanned input bit. -/
  next : Cfg → Bool → Cfg
  /-- The output of a halting configuration; `none` for non-halting configurations. -/
  out : Cfg → Option Bool
  /-- Once the machine has halted it stays halted with the same output. -/
  out_sticky : ∀ c b, (out c).isSome = true → out (next c b) = out c

attribute [instance] DSM.fintypeCfg

/-- One step of a deterministic machine on input `x`. -/
def DSM.trans (M : DSM) (x : List Bool) (c : M.Cfg) : M.Cfg :=
  M.next c (bitAt x (M.head c))

/-- The configuration of a deterministic machine after `t` steps on input `x`. -/
def DSM.run (M : DSM) (x : List Bool) (t : ℕ) : M.Cfg :=
  (M.trans x)^[t] M.start

/-- A deterministic machine outputs `v` on `x` if it halts with output `v`. -/
def DSM.Outputs (M : DSM) (x : List Bool) (v : Bool) : Prop :=
  ∃ t, M.out (M.run x t) = some v

/-- The class `NSPACE f`: languages recognized by nondeterministic machines with at most
`2 ^ f n` configurations on inputs of length `n` (i.e. space `f n`). -/
def NSPACE (f : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∀ n : ℕ, ∃ M : NSM, Fintype.card M.Cfg ≤ 2 ^ f n ∧
        ∀ x : List Bool, x.length = n → (x ∈ L ↔ M.Accepts x)}

/-- The class `DSPACE f`: languages decided by deterministic machines with at most `2 ^ f n`
configurations on inputs of length `n` (i.e. space `f n`). -/
def DSPACE (f : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∀ n : ℕ, ∃ M : DSM, Fintype.card M.Cfg ≤ 2 ^ f n ∧
        ∀ x : List Bool, x.length = n → ∃ v, M.Outputs x v ∧ (v = true ↔ x ∈ L)}

/-- Polynomial space. -/
def PSPACE : Set (Set (List Bool)) := {L | ∃ k c : ℕ, L ∈ DSPACE (fun n => c * (n + 1) ^ k)}

/-- Nondeterministic polynomial space. -/
def NPSPACE : Set (Set (List Bool)) := {L | ∃ k c : ℕ, L ∈ NSPACE (fun n => c * (n + 1) ^ k)}

end CS

namespace CS

/-! ## Bounded reachability in a finite configuration graph -/

section Reach

variable {C : Type} [Fintype C] [DecidableEq C] (E : C → C → Bool)

/-- `reachB E t a b` : `b` can be reached from `a` in at most `t` steps. -/
def reachB : ℕ → C → C → Bool
  | 0, a, b => decide (a = b)
  | t + 1, a, b => reachB t a b || decide (∃ m, reachB t a m = true ∧ E m b = true)

/-- Savitch's middle-first predicate: `RkB E k a b` says that `b` is reachable from `a`
in at most `2 ^ k` steps, computed by recursively guessing a midpoint. -/
def RkB : ℕ → C → C → Bool
  | 0, a, b => decide (a = b) || E a b
  | k + 1, a, b => decide (∃ m, RkB k a m = true ∧ RkB k m b = true)

variable {E}

lemma reachB_zero (a b : C) : reachB E 0 a b = decide (a = b) := rfl

lemma reachB_succ (t : ℕ) (a b : C) :
    reachB E (t + 1) a b = (reachB E t a b || decide (∃ m, reachB E t a m = true ∧ E m b = true)) :=
  rfl

lemma reachB_self (t : ℕ) (a : C) : reachB E t a a = true := by
  induction t with
  | zero => simp [reachB]
  | succ t ih => simp [reachB_succ, ih]

lemma reachB_mono_succ {t : ℕ} {a b : C} (h : reachB E t a b = true) :
    reachB E (t + 1) a b = true := by
  simp [reachB_succ, h]

lemma reachB_mono {t u : ℕ} {a b : C} (htu : t ≤ u) (h : reachB E t a b = true) :
    reachB E u a b = true := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le htu
  clear htu
  induction v with
  | zero => simpa using h
  | succ v ih =>
      rw [show t + (v + 1) = (t + v) + 1 from rfl]
      exact reachB_mono_succ ih

lemma reachB_add (t u : ℕ) (a b : C) :
    reachB E (t + u) a b = true ↔ ∃ m, reachB E t a m = true ∧ reachB E u m b = true := by
  induction u generalizing b with
  | zero =>
      constructor
      · intro h; exact ⟨b, h, by simp [reachB]⟩
      · rintro ⟨m, hm, hmb⟩
        simp only [reachB, decide_eq_true_eq] at hmb
        subst hmb; simpa using hm
  | succ u ih =>
      constructor
      · intro h
        rw [show t + (u + 1) = (t + u) + 1 from rfl, reachB_succ] at h
        rcases Bool.or_eq_true_iff.mp h with h | h
        · obtain ⟨m, hm, hmb⟩ := (ih b).mp h
          exact ⟨m, hm, reachB_mono_succ hmb⟩
        · simp only [decide_eq_true_eq] at h
          obtain ⟨w, hw, hwb⟩ := h
          obtain ⟨m, hm, hmw⟩ := (ih w).mp hw
          refine ⟨m, hm, ?_⟩
          rw [reachB_succ]
          simp only [Bool.or_eq_true_iff, decide_eq_true_eq]
          exact Or.inr ⟨w, hmw, hwb⟩
      · rintro ⟨m, hm, hmb⟩
        rw [reachB_succ] at hmb
        rw [show t + (u + 1) = (t + u) + 1 from rfl, reachB_succ]
        simp only [Bool.or_eq_true_iff, decide_eq_true_eq]
        rcases Bool.or_eq_true_iff.mp hmb with h | h
        · exact Or.inl ((ih b).mpr ⟨m, hm, h⟩)
        · simp only [decide_eq_true_eq] at h
          obtain ⟨w, hw, hwb⟩ := h
          exact Or.inr ⟨w, (ih w).mpr ⟨m, hm, hw⟩, hwb⟩

lemma RkB_iff_reachB (k : ℕ) (a b : C) :
    RkB E k a b = true ↔ reachB E (2 ^ k) a b = true := by
  induction k generalizing a b with
  | zero =>
      constructor
      · intro h
        simp only [RkB, Bool.or_eq_true_iff, decide_eq_true_eq] at h
        rcases h with h | h
        · subst h; exact reachB_self _ _
        · rw [show (2 : ℕ) ^ 0 = 0 + 1 by norm_num, reachB_succ]
          simp only [Bool.or_eq_true_iff, decide_eq_true_eq]
          exact Or.inr ⟨a, by simp [reachB_zero], h⟩
      · intro h
        rw [show (2 : ℕ) ^ 0 = 0 + 1 by norm_num, reachB_succ] at h
        simp only [reachB_zero, Bool.or_eq_true_iff, decide_eq_true_eq] at h
        simp only [RkB, Bool.or_eq_true_iff, decide_eq_true_eq]
        rcases h with h | ⟨m, hm, hmb⟩
        · exact Or.inl h
        · subst hm; exact Or.inr hmb
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      simp only [RkB, decide_eq_true_eq, hpow, reachB_add]
      constructor
      · rintro ⟨m, h1, h2⟩; exact ⟨m, (ih a m).mp h1, (ih m b).mp h2⟩
      · rintro ⟨m, h1, h2⟩; exact ⟨m, (ih a m).mpr h1, (ih m b).mpr h2⟩

lemma reachB_iff_reflTransGen (a b : C) :
    (∃ t, reachB E t a b = true) ↔ Relation.ReflTransGen (fun a b => E a b = true) a b := by
  constructor
  · rintro ⟨t, ht⟩
    induction t generalizing b with
    | zero =>
        simp only [reachB_zero, decide_eq_true_eq] at ht
        subst ht; exact Relation.ReflTransGen.refl
    | succ t ih =>
        rw [reachB_succ] at ht
        rcases Bool.or_eq_true_iff.mp ht with h | h
        · exact ih b h
        · simp only [decide_eq_true_eq] at h
          obtain ⟨m, hm, hmb⟩ := h
          exact Relation.ReflTransGen.tail (ih m hm) hmb
  · intro h
    induction h with
    | refl => exact ⟨0, by simp [reachB_zero]⟩
    | tail hab hbc ih =>
        obtain ⟨t, ht⟩ := ih
        refine ⟨t + 1, ?_⟩
        rw [reachB_succ]
        simp only [Bool.or_eq_true_iff, decide_eq_true_eq]
        exact Or.inr ⟨_, ht, hbc⟩

/-- The set of configurations reachable from `a` in at most `t` steps. -/
def reachSet (E : C → C → Bool) (a : C) (t : ℕ) : Finset C :=
  Finset.univ.filter (fun b => reachB E t a b = true)

lemma mem_reachSet {a b : C} {t : ℕ} : b ∈ reachSet E a t ↔ reachB E t a b = true := by
  simp [reachSet]

/-- One step of the closure operation on sets of configurations. -/
def stepSet (E : C → C → Bool) (X : Finset C) : Finset C :=
  X ∪ Finset.univ.filter (fun b => ∃ m ∈ X, E m b = true)

lemma reachSet_succ (a : C) (t : ℕ) :
    reachSet E a (t + 1) = stepSet E (reachSet E a t) := by
  ext b
  simp [reachSet, stepSet, reachB_succ]

lemma reachSet_subset_succ (a : C) (t : ℕ) : reachSet E a t ⊆ reachSet E a (t + 1) := by
  intro b hb
  rw [reachSet_succ]
  exact Finset.mem_union_left _ hb

lemma reachSet_stab {a : C} {t : ℕ} (h : reachSet E a t = reachSet E a (t + 1)) :
    ∀ u, reachSet E a (t + u) = reachSet E a t := by
  intro u
  induction u with
  | zero => rfl
  | succ u ih =>
      have : reachSet E a (t + u + 1) = stepSet E (reachSet E a (t + u)) := reachSet_succ a _
      rw [show t + (u + 1) = (t + u) + 1 from rfl, this, ih, ← reachSet_succ, ← h]

lemma reachSet_card_ge {a : C} (t : ℕ) (h : ∀ u < t, reachSet E a u ≠ reachSet E a (u + 1)) :
    t + 1 ≤ (reachSet E a t).card := by
  induction t with
  | zero =>
      have : reachSet E a 0 = {a} := by
        ext b; simp [reachSet, reachB_zero, eq_comm]
      simp [this]
  | succ t ih =>
      have h1 : t + 1 ≤ (reachSet E a t).card := ih (fun u hu => h u (by omega))
      have h2 : reachSet E a t ⊂ reachSet E a (t + 1) :=
        ⟨reachSet_subset_succ a t, fun hsub =>
          h t (by omega) (Finset.Subset.antisymm (reachSet_subset_succ a t) hsub)⟩
      have := Finset.card_lt_card h2
      omega

lemma reachB_card {a b : C} {t : ℕ} (h : reachB E t a b = true) :
    reachB E (Fintype.card C) a b = true := by
  set N := Fintype.card C with hN
  by_cases hstab : ∀ u < N, reachSet E a u ≠ reachSet E a (u + 1)
  · exfalso
    have h1 : N + 1 ≤ (reachSet E a N).card := reachSet_card_ge N hstab
    have h2 : (reachSet E a N).card ≤ N := by
      simpa [hN] using Finset.card_le_univ (reachSet E a N)
    omega
  · push_neg at hstab
    obtain ⟨u, huN, hu⟩ := hstab
    have hconst : ∀ v, reachSet E a (u + v) = reachSet E a u := reachSet_stab hu
    have hbN : reachSet E a N = reachSet E a u := by
      have := hconst (N - u)
      rwa [show u + (N - u) = N by omega] at this
    rcases Nat.lt_or_ge t N with htN | htN
    · exact reachB_mono (le_of_lt htN) h
    · have hb : b ∈ reachSet E a t := mem_reachSet.mpr h
      have : reachSet E a t = reachSet E a u := by
        have := hconst (t - u)
        rwa [show u + (t - u) = t by omega] at this
      rw [this, ← hbN] at hb
      exact mem_reachSet.mp hb

end Reach

end CS

namespace CS

/-! ## Adding a unique accepting configuration -/

section Sink

variable (M : NSM)

/-- Edges of the configuration graph of `M` extended by a single absorbing accepting
configuration `none`. -/
def NSM.edge' (a : Option M.Cfg) (t : Bool) (b : Option M.Cfg) : Bool :=
  match a, b with
  | some a, some b => M.step a t b
  | some a, none => M.acc a
  | none, _ => false

/-- Input head position of the extended machine. -/
def NSM.head' : Option M.Cfg → ℕ
  | some a => M.head a
  | none => 0

/-- The extended configuration graph on the input `x`. -/
def NSM.E' (x : List Bool) (a b : Option M.Cfg) : Bool :=
  M.edge' a (bitAt x (M.head' a)) b

variable {M}

lemma NSM.accepts_iff_reach (x : List Bool) :
    M.Accepts x ↔
      Relation.ReflTransGen (fun a b => M.E' x a b = true) (some M.start) none := by
  classical
  constructor
  · rintro ⟨c, hacc, hpath⟩
    have lift : ∀ a b : M.Cfg, Relation.ReflTransGen (M.Edge x) a b →
        Relation.ReflTransGen (fun a b => M.E' x a b = true) (some a) (some b) := by
      intro a b h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact ih.tail hbc
    exact (lift _ _ hpath).tail (by simpa [NSM.E', NSM.edge'] using hacc)
  · intro h
    have key : ∀ c : Option M.Cfg,
        Relation.ReflTransGen (fun a b => M.E' x a b = true) (some M.start) c →
        ((∀ a, c = some a → Relation.ReflTransGen (M.Edge x) M.start a) ∧
          (c = none → M.Accepts x)) := by
      intro c hc
      induction hc with
      | refl =>
          refine ⟨fun a ha => ?_, fun ha => by cases ha⟩
          cases ha; exact Relation.ReflTransGen.refl
      | @tail b c _ hbc ih =>
          cases b with
          | none => simp [NSM.E', NSM.edge'] at hbc
          | some a =>
              have hpa : Relation.ReflTransGen (M.Edge x) M.start a := ih.1 a rfl
              cases c with
              | none =>
                  refine ⟨fun z hz => (by cases hz), fun _ => ?_⟩
                  exact ⟨a, by simpa [NSM.E', NSM.edge'] using hbc, hpa⟩
              | some e =>
                  refine ⟨fun z hz => ?_, fun hz => (by cases hz)⟩
                  cases hz
                  exact hpa.tail (by simpa [NSM.E', NSM.edge', NSM.Edge, NSM.head'] using hbc)
    exact (key none h).2 rfl

end Sink

/-! ## Finiteness of bounded-length lists -/

section BoundedLists

variable {α : Type} [Fintype α] (n : ℕ)

/-- Encoding of a list of length at most `n` by its optional entries. -/
def listLeEnc (l : {l : List α // l.length ≤ n}) : Fin n → Option α := fun i => l.val[(i : ℕ)]?

omit [Fintype α] in
lemma listLeEnc_injective : Function.Injective (listLeEnc (α := α) n) := by
  intro l₁ l₂ h
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · exact congrFun h ⟨i, hi⟩
  · rw [List.getElem?_eq_none (le_trans l₁.2 (by omega)),
      List.getElem?_eq_none (le_trans l₂.2 (by omega))]

noncomputable instance instFintypeListLe : Fintype {l : List α // l.length ≤ n} :=
  Fintype.ofInjective _ (listLeEnc_injective n)

lemma card_listLe_le :
    Fintype.card {l : List α // l.length ≤ n} ≤ (Fintype.card α + 1) ^ n := by
  have h := Fintype.card_le_of_injective _ (listLeEnc_injective (α := α) n)
  simpa using h

end BoundedLists

end CS

namespace CS

/-! ## The deterministic Savitch machine

The deterministic machine implements the usual recursive procedure
`R k a b = ∃ m, R (k-1) a m ∧ R (k-1) m b` by an explicit stack of at most `d + 1` frames.
Each frame stores the two endpoints of the call, the index of the midpoint candidate currently
being tried, and a phase (0: start the first recursive call, 1: first call has returned,
2: second call has returned).  The recursion depth of a frame is determined by its position in
the stack, so it need not be stored. -/

section Savitch

/-- The number of configurations of the extended machine. -/
def NN (M : NSM) : ℕ := Fintype.card (Option M.Cfg)

lemma NN_pos (M : NSM) : 0 < NN M := Fintype.card_pos (α := Option M.Cfg)

/-- A stack frame of the deterministic Savitch machine. -/
abbrev Frame (M : NSM) : Type := Option M.Cfg × Option M.Cfg × Fin (NN M + 1) × Fin 3

/-- The `z`-th configuration of the extended machine (junk for out-of-range `z`). -/
noncomputable def cand (M : NSM) (z : ℕ) : Option M.Cfg :=
  if h : z < NN M then (Fintype.equivFin (Option M.Cfg)).symm ⟨z, by simpa [NN] using h⟩ else none

lemma cand_surj (M : NSM) (m : Option M.Cfg) : ∃ z, z < NN M ∧ cand M z = m := by
  refine ⟨(Fintype.equivFin (Option M.Cfg) m : ℕ), by simpa [NN] using (Fintype.equivFin (Option M.Cfg) m).isLt, ?_⟩
  have h : ((Fintype.equivFin (Option M.Cfg) m : ℕ)) < NN M := by
    simpa [NN] using (Fintype.equivFin (Option M.Cfg) m).isLt
  simp [cand, h]

/-- Increment of a candidate index. -/
def incF (M : NSM) (i : Fin (NN M + 1)) : Fin (NN M + 1) :=
  if h : (i : ℕ) < NN M then ⟨(i : ℕ) + 1, by omega⟩ else i

lemma incF_val {M : NSM} {i : Fin (NN M + 1)} (h : (i : ℕ) < NN M) :
    ((incF M i : Fin (NN M + 1)) : ℕ) = (i : ℕ) + 1 := by
  simp [incF, h]

/-- One step of the Savitch machine, described on raw (unbounded) stacks. -/
noncomputable def rawStep (M : NSM) (d : ℕ) (c : List (Frame M) × Bool) (t : Bool) : List (Frame M) × Bool :=
  match c.1 with
  | [] => c
  | (a, b, i, ph) :: rest =>
      if d + 1 - (rest.length + 1) = 0 then (rest, decide (a = b) || M.edge' a t b)
      else if (ph : ℕ) = 0 then
        (if (i : ℕ) < NN M then
            (((a, cand M (i : ℕ), 0, 0) : Frame M) :: ((a, b, i, 1) : Frame M) :: rest, c.2)
          else (rest, false))
      else if (ph : ℕ) = 1 then
        (if c.2 = true then
            (((cand M (i : ℕ), b, 0, 0) : Frame M) :: ((a, b, i, 2) : Frame M) :: rest, c.2)
          else (((a, b, incF M i, 0) : Frame M) :: rest, false))
      else
        (if c.2 = true then (rest, true)
          else (((a, b, incF M i, 0) : Frame M) :: rest, false))

/-- The input position scanned in a raw configuration. -/
def rawHead (M : NSM) (l : List (Frame M)) : ℕ :=
  match l with
  | [] => 0
  | (a, _, _, _) :: _ => M.head' a

/-- Configurations of the deterministic Savitch machine of depth `d`. -/
def SavCfg (M : NSM) (d : ℕ) : Type := {l : List (Frame M) // l.length ≤ d + 1} × Bool

noncomputable instance (M : NSM) (d : ℕ) : Fintype (SavCfg M d) :=
  inferInstanceAs (Fintype ({l : List (Frame M) // l.length ≤ d + 1} × Bool))

/-- The raw data of a configuration of the Savitch machine. -/
def valOf {M : NSM} {d : ℕ} (c : SavCfg M d) : List (Frame M) × Bool := (c.1.val, c.2)

/-- The deterministic Savitch machine of depth `d` associated with `M`. -/
noncomputable def savDSM (M : NSM) (d : ℕ) : DSM where
  Cfg := SavCfg M d
  fintypeCfg := inferInstance
  start := (⟨[((some M.start, none, 0, 0) : Frame M)], by simp⟩, false)
  head := fun c => rawHead M c.1.val
  next := fun c t =>
    let r := rawStep M d (c.1.val, c.2) t
    if h : r.1.length ≤ d + 1 then (⟨r.1, h⟩, r.2) else c
  out := fun c => match c.1.val with | [] => some c.2 | _ => none
  out_sticky := by
    rintro ⟨⟨l, hl⟩, r⟩ t hout
    cases l with
    | cons f rest => simp at hout
    | nil => simp [rawStep]

lemma savDSM_out {M : NSM} {d : ℕ} (c : SavCfg M d) :
    (savDSM M d).out c = match c.1.val with | [] => some c.2 | _ => none := rfl

/-- A single step of the Savitch machine, computed on raw data. -/
lemma sav_step {M : NSM} {d : ℕ} (x : List Bool) (c : SavCfg M d)
    (h : (rawStep M d (valOf c) (bitAt x (rawHead M c.1.val))).1.length ≤ d + 1) :
    valOf ((savDSM M d).trans x c) = rawStep M d (valOf c) (bitAt x (rawHead M c.1.val)) := by
  simp only [DSM.trans, savDSM, valOf] at *
  rw [dif_pos h]

end Savitch

end CS

namespace CS

section SavitchSteps

variable {M : NSM} {d : ℕ} (x : List Bool)

lemma stack_len {c : SavCfg M d} {a b : Option M.Cfg} {i : Fin (NN M + 1)} {ph : Fin 3}
    {rest : List (Frame M)} (hc : c.1.val = ((a, b, i, ph) : Frame M) :: rest) :
    rest.length + 1 ≤ d + 1 := by
  have := c.1.property
  rw [hc] at this
  simpa using this

lemma step_pop0 (c : SavCfg M d) (a b : Option M.Cfg) (i : Fin (NN M + 1)) (ph : Fin 3)
    (rest : List (Frame M)) (hc : c.1.val = ((a, b, i, ph) : Frame M) :: rest)
    (hk : d + 1 - (rest.length + 1) = 0) :
    valOf ((savDSM M d).trans x c) =
      (rest, decide (a = b) || M.edge' a (bitAt x (M.head' a)) b) := by
  have hlen := stack_len hc
  have hk2 : d - rest.length = 0 := by omega
  have hraw : rawStep M d (valOf c) (bitAt x (rawHead M c.1.val))
      = (rest, decide (a = b) || M.edge' a (bitAt x (M.head' a)) b) := by
    simp [rawStep, valOf, hc, rawHead, hk2]
  rw [sav_step x c (by rw [hraw]; simp only [List.length_cons]; omega)]
  exact hraw

lemma step_push0 (c : SavCfg M d) (a b : Option M.Cfg) (i : Fin (NN M + 1))
    (rest : List (Frame M)) (hc : c.1.val = ((a, b, i, 0) : Frame M) :: rest)
    (hlen2 : rest.length + 2 ≤ d + 1) (hi : (i : ℕ) < NN M) :
    valOf ((savDSM M d).trans x c) =
      (((a, cand M (i : ℕ), 0, 0) : Frame M) :: ((a, b, i, 1) : Frame M) :: rest, c.2) := by
  have hk2 : ¬ (d - rest.length = 0) := by omega
  have hraw : rawStep M d (valOf c) (bitAt x (rawHead M c.1.val))
      = (((a, cand M (i : ℕ), 0, 0) : Frame M) :: ((a, b, i, 1) : Frame M) :: rest, c.2) := by
    simp [rawStep, valOf, hc, rawHead, hk2, hi]
  rw [sav_step x c (by rw [hraw]; simp only [List.length_cons]; omega)]
  exact hraw

lemma step_exhaust (c : SavCfg M d) (a b : Option M.Cfg) (i : Fin (NN M + 1))
    (rest : List (Frame M)) (hc : c.1.val = ((a, b, i, 0) : Frame M) :: rest)
    (hk : d + 1 - (rest.length + 1) ≠ 0) (hi : ¬ (i : ℕ) < NN M) :
    valOf ((savDSM M d).trans x c) = (rest, false) := by
  have hlen := stack_len hc
  have hk2 : ¬ (d - rest.length = 0) := by omega
  have hraw : rawStep M d (valOf c) (bitAt x (rawHead M c.1.val)) = (rest, false) := by
    simp [rawStep, valOf, hc, rawHead, hk2, hi]
  rw [sav_step x c (by rw [hraw]; simp only [List.length_cons]; omega)]
  exact hraw

lemma step_ph1_true (c : SavCfg M d) (a b : Option M.Cfg) (i : Fin (NN M + 1))
    (rest : List (Frame M)) (hc : c.1.val = ((a, b, i, 1) : Frame M) :: rest)
    (hlen2 : rest.length + 2 ≤ d + 1) (hr : c.2 = true) :
    valOf ((savDSM M d).trans x c) =
      (((cand M (i : ℕ), b, 0, 0) : Frame M) :: ((a, b, i, 2) : Frame M) :: rest, true) := by
  have hk2 : ¬ (d - rest.length = 0) := by omega
  have hraw : rawStep M d (valOf c) (bitAt x (rawHead M c.1.val))
      = (((cand M (i : ℕ), b, 0, 0) : Frame M) :: ((a, b, i, 2) : Frame M) :: rest, true) := by
    simp [rawStep, valOf, hc, rawHead, hk2, hr]
  rw [sav_step x c (by rw [hraw]; simp only [List.length_cons]; omega)]
  exact hraw

lemma step_ph1_false (c : SavCfg M d) (a b : Option M.Cfg) (i : Fin (NN M + 1))
    (rest : List (Frame M)) (hc : c.1.val = ((a, b, i, 1) : Frame M) :: rest)
    (hk : d + 1 - (rest.length + 1) ≠ 0) (hr : c.2 = false) :
    valOf ((savDSM M d).trans x c) = (((a, b, incF M i, 0) : Frame M) :: rest, false) := by
  have hlen := stack_len hc
  have hk2 : ¬ (d - rest.length = 0) := by omega
  have hraw : rawStep M d (valOf c) (bitAt x (rawHead M c.1.val))
      = (((a, b, incF M i, 0) : Frame M) :: rest, false) := by
    simp [rawStep, valOf, hc, rawHead, hk2, hr]
  rw [sav_step x c (by rw [hraw]; simp only [List.length_cons]; omega)]
  exact hraw

lemma step_ph2_true (c : SavCfg M d) (a b : Option M.Cfg) (i : Fin (NN M + 1))
    (rest : List (Frame M)) (hc : c.1.val = ((a, b, i, 2) : Frame M) :: rest)
    (hk : d + 1 - (rest.length + 1) ≠ 0) (hr : c.2 = true) :
    valOf ((savDSM M d).trans x c) = (rest, true) := by
  have hlen := stack_len hc
  have hk2 : ¬ (d - rest.length = 0) := by omega
  have hraw : rawStep M d (valOf c) (bitAt x (rawHead M c.1.val)) = (rest, true) := by
    simp [rawStep, valOf, hc, rawHead, hk2, hr]
  rw [sav_step x c (by rw [hraw]; simp only [List.length_cons]; omega)]
  exact hraw

lemma step_ph2_false (c : SavCfg M d) (a b : Option M.Cfg) (i : Fin (NN M + 1))
    (rest : List (Frame M)) (hc : c.1.val = ((a, b, i, 2) : Frame M) :: rest)
    (hk : d + 1 - (rest.length + 1) ≠ 0) (hr : c.2 = false) :
    valOf ((savDSM M d).trans x c) = (((a, b, incF M i, 0) : Frame M) :: rest, false) := by
  have hlen := stack_len hc
  have hk2 : ¬ (d - rest.length = 0) := by omega
  have hraw : rawStep M d (valOf c) (bitAt x (rawHead M c.1.val))
      = (((a, b, incF M i, 0) : Frame M) :: rest, false) := by
    simp [rawStep, valOf, hc, rawHead, hk2, hr]
  rw [sav_step x c (by rw [hraw]; simp only [List.length_cons]; omega)]
  exact hraw

end SavitchSteps

end CS

namespace CS

section SavitchCorrect

variable {M : NSM} {d : ℕ} (x : List Bool)

lemma bool_eq_of_iff {v w : Bool} (h : v = true ↔ w = true) : v = w := by
  cases v <;> cases w <;> simp_all

lemma valOf_fst {c : SavCfg M d} {L : List (Frame M)} {v : Bool} (h : valOf c = (L, v)) :
    c.1.val = L := congrArg Prod.fst h

lemma valOf_snd {c : SavCfg M d} {L : List (Frame M)} {v : Bool} (h : valOf c = (L, v)) :
    c.2 = v := congrArg Prod.snd h

/-- Correctness of a recursive call of the Savitch machine: started on a frame `(a, b, 0, 0)`
at recursion level `k`, the machine eventually pops that frame, returning `RkB _ k a b`. -/
lemma sav_call (k : ℕ) : ∀ (a b : Option M.Cfg) (rest : List (Frame M)) (c : SavCfg M d),
    c.1.val = ((a, b, 0, 0) : Frame M) :: rest → d + 1 - (rest.length + 1) = k →
    ∃ t, valOf (((savDSM M d).trans x)^[t] c) = (rest, RkB (M.E' x) k a b) := by
  induction k with
  | zero =>
      intro a b rest c hc hk
      refine ⟨1, ?_⟩
      have h := step_pop0 x c a b 0 0 rest hc hk
      simpa [Function.iterate_one, RkB, NSM.E'] using h
  | succ k ih =>
      have loop : ∀ (j : ℕ) (a b : Option M.Cfg) (i : Fin (NN M + 1)) (rest : List (Frame M))
          (c : SavCfg M d), c.1.val = ((a, b, i, 0) : Frame M) :: rest →
          d + 1 - (rest.length + 1) = k + 1 → NN M - (i : ℕ) ≤ j →
          ∃ t, (valOf (((savDSM M d).trans x)^[t] c)).1 = rest ∧
            ((valOf (((savDSM M d).trans x)^[t] c)).2 = true ↔
              ∃ z, (i : ℕ) ≤ z ∧ z < NN M ∧ RkB (M.E' x) k a (cand M z) = true ∧
                RkB (M.E' x) k (cand M z) b = true) := by
        intro j
        induction j with
        | zero =>
            intro a b i rest c hc hk hj
            refine ⟨1, ?_⟩
            have h := step_exhaust x c a b i rest hc (by omega) (by omega)
            rw [Function.iterate_one, h]
            refine ⟨rfl, ?_⟩
            simp only [Bool.false_eq_true, false_iff, not_exists]
            rintro z ⟨hz1, hz2, -, -⟩
            omega
        | succ j ihj =>
            intro a b i rest c hc hk hj
            by_cases hi : (i : ℕ) < NN M
            · -- start the recursive calls for the candidate midpoint `cand M i`
              have hlen2 : rest.length + 2 ≤ d + 1 := by omega
              set f := (savDSM M d).trans x with hf
              have h1 := step_push0 x c a b i rest hc hlen2 hi
              rw [← hf] at h1
              obtain ⟨t2, ht2⟩ := ih a (cand M (i : ℕ)) (((a, b, i, 1) : Frame M) :: rest) (f c)
                (valOf_fst h1) (by simp only [List.length_cons]; omega)
              by_cases hv1 : RkB (M.E' x) k a (cand M (i : ℕ)) = true
              · have h3 := step_ph1_true x (f^[t2] (f c)) a b i rest (valOf_fst ht2) hlen2
                  (by rw [valOf_snd ht2]; exact hv1)
                rw [← hf] at h3
                obtain ⟨t4, ht4⟩ := ih (cand M (i : ℕ)) b (((a, b, i, 2) : Frame M) :: rest)
                  (f (f^[t2] (f c))) (valOf_fst h3) (by simp only [List.length_cons]; omega)
                by_cases hv2 : RkB (M.E' x) k (cand M (i : ℕ)) b = true
                · have h5 := step_ph2_true x (f^[t4] (f (f^[t2] (f c)))) a b i rest
                    (valOf_fst ht4) (by omega) (by rw [valOf_snd ht4]; exact hv2)
                  rw [← hf] at h5
                  refine ⟨1 + (t4 + (1 + (t2 + 1))), ?_⟩
                  rw [Function.iterate_add_apply f 1, Function.iterate_add_apply f t4,
                    Function.iterate_add_apply f 1, Function.iterate_add_apply f t2 1]
                  simp only [Function.iterate_one]
                  rw [h5]
                  exact ⟨rfl, iff_of_true rfl ⟨(i : ℕ), le_rfl, hi, hv1, hv2⟩⟩
                · have hv2' : RkB (M.E' x) k (cand M (i : ℕ)) b = false := by simpa using hv2
                  have h5 := step_ph2_false x (f^[t4] (f (f^[t2] (f c)))) a b i rest
                    (valOf_fst ht4) (by omega) (by rw [valOf_snd ht4]; exact hv2')
                  rw [← hf] at h5
                  obtain ⟨t6, ht6⟩ := ihj a b (incF M i) rest (f (f^[t4] (f (f^[t2] (f c)))))
                    (valOf_fst h5) hk (by rw [incF_val hi]; omega)
                  refine ⟨t6 + (1 + (t4 + (1 + (t2 + 1)))), ?_⟩
                  rw [Function.iterate_add_apply f t6, Function.iterate_add_apply f 1,
                    Function.iterate_add_apply f t4, Function.iterate_add_apply f 1,
                    Function.iterate_add_apply f t2 1]
                  simp only [Function.iterate_one]
                  refine ⟨ht6.1, ?_⟩
                  rw [ht6.2, incF_val hi]
                  constructor
                  · rintro ⟨z, hz1, hz2, hz3, hz4⟩
                    exact ⟨z, by omega, hz2, hz3, hz4⟩
                  · rintro ⟨z, hz1, hz2, hz3, hz4⟩
                    rcases Nat.eq_or_lt_of_le hz1 with h | h
                    · rw [← h] at hz4; rw [hv2'] at hz4; exact absurd hz4 (by simp)
                    · exact ⟨z, by omega, hz2, hz3, hz4⟩
              · have hv1' : RkB (M.E' x) k a (cand M (i : ℕ)) = false := by simpa using hv1
                have h3 := step_ph1_false x (f^[t2] (f c)) a b i rest (valOf_fst ht2) (by omega)
                  (by rw [valOf_snd ht2]; exact hv1')
                rw [← hf] at h3
                obtain ⟨t4, ht4⟩ := ihj a b (incF M i) rest (f (f^[t2] (f c)))
                  (valOf_fst h3) hk (by rw [incF_val hi]; omega)
                refine ⟨t4 + (1 + (t2 + 1)), ?_⟩
                rw [Function.iterate_add_apply f t4, Function.iterate_add_apply f 1,
                  Function.iterate_add_apply f t2 1]
                simp only [Function.iterate_one]
                refine ⟨ht4.1, ?_⟩
                rw [ht4.2, incF_val hi]
                constructor
                · rintro ⟨z, hz1, hz2, hz3, hz4⟩
                  exact ⟨z, by omega, hz2, hz3, hz4⟩
                · rintro ⟨z, hz1, hz2, hz3, hz4⟩
                  rcases Nat.eq_or_lt_of_le hz1 with h | h
                  · rw [← h] at hz3; rw [hv1'] at hz3; exact absurd hz3 (by simp)
                  · exact ⟨z, by omega, hz2, hz3, hz4⟩
            · refine ⟨1, ?_⟩
              have h := step_exhaust x c a b i rest hc (by omega) hi
              rw [Function.iterate_one, h]
              refine ⟨rfl, ?_⟩
              simp only [Bool.false_eq_true, false_iff, not_exists]
              rintro z ⟨hz1, hz2, -, -⟩
              omega
      intro a b rest c hc hk
      obtain ⟨t, ht1, ht2⟩ := loop (NN M) a b 0 rest c hc hk (by simp)
      refine ⟨t, ?_⟩
      refine Prod.ext ht1 (bool_eq_of_iff ?_)
      rw [ht2]
      constructor
      · rintro ⟨z, -, -, hz3, hz4⟩
        simpa [RkB] using ⟨cand M z, hz3, hz4⟩
      · intro h
        simp only [RkB, decide_eq_true_eq] at h
        obtain ⟨m, hm1, hm2⟩ := h
        obtain ⟨z, hz, hzm⟩ := cand_surj M m
        exact ⟨z, by simp, hz, by rw [hzm]; exact hm1, by rw [hzm]; exact hm2⟩

end SavitchCorrect

end CS

namespace CS

section SavitchMain

/-- The Savitch machine halts with the value of the middle-first predicate at depth `d`. -/
lemma sav_outputs (M : NSM) (d : ℕ) (x : List Bool) :
    (savDSM M d).Outputs x (RkB (M.E' x) d (some M.start) none) := by
  obtain ⟨t, ht⟩ := sav_call x d (some M.start) none [] (savDSM M d).start rfl (by simp)
  refine ⟨t, ?_⟩
  have h1 : (((savDSM M d).trans x)^[t] (savDSM M d).start).1.val = [] := valOf_fst ht
  have h2 : (((savDSM M d).trans x)^[t] (savDSM M d).start).2
      = RkB (M.E' x) d (some M.start) none := valOf_snd ht
  rw [DSM.run, savDSM_out, h1, ← h2]

lemma RkB_iff_accepts (M : NSM) (d : ℕ) (hcard : NN M ≤ 2 ^ d) (x : List Bool) :
    RkB (M.E' x) d (some M.start) none = true ↔ M.Accepts x := by
  rw [NSM.accepts_iff_reach, RkB_iff_reachB]
  constructor
  · intro h
    exact (reachB_iff_reflTransGen _ _).mp ⟨_, h⟩
  · intro h
    obtain ⟨t, ht⟩ := (reachB_iff_reflTransGen _ _).mpr h
    exact reachB_mono hcard (reachB_card ht)

lemma card_savCfg_le (M : NSM) (d : ℕ) (hA : NN M ≤ 2 ^ d) :
    Fintype.card (SavCfg M d) ≤ 2 ^ ((3 * d + 3) * (d + 1) + 1) := by
  have hA1 : 1 ≤ NN M := NN_pos M
  have hframe : Fintype.card (Frame M) + 1 ≤ 2 ^ (3 * d + 3) := by
    have hcf : Fintype.card (Frame M) = NN M * (NN M * ((NN M + 1) * 3)) := by
      simp [Frame, NN, Fintype.card_prod]
    have h8 : NN M * (NN M * ((NN M + 1) * 3)) + 1 ≤ 8 * NN M ^ 3 := by nlinarith
    have hpow : (8 : ℕ) * NN M ^ 3 ≤ 2 ^ (3 * d + 3) := by
      have : NN M ^ 3 ≤ (2 ^ d) ^ 3 := Nat.pow_le_pow_left hA 3
      calc 8 * NN M ^ 3 ≤ 8 * (2 ^ d) ^ 3 := by omega
        _ = 2 ^ (3 * d + 3) := by rw [← pow_mul]; ring
    omega
  have hcard : Fintype.card (SavCfg M d)
      = Fintype.card {l : List (Frame M) // l.length ≤ d + 1} * 2 := by
    show Fintype.card ({l : List (Frame M) // l.length ≤ d + 1} × Bool) = _
    simp [Fintype.card_prod]
  have hlist : Fintype.card {l : List (Frame M) // l.length ≤ d + 1}
      ≤ (Fintype.card (Frame M) + 1) ^ (d + 1) := card_listLe_le (d + 1)
  calc Fintype.card (SavCfg M d)
      = Fintype.card {l : List (Frame M) // l.length ≤ d + 1} * 2 := hcard
    _ ≤ (Fintype.card (Frame M) + 1) ^ (d + 1) * 2 := by omega
    _ ≤ (2 ^ (3 * d + 3)) ^ (d + 1) * 2 := by
        exact Nat.mul_le_mul_right 2 (Nat.pow_le_pow_left hframe (d + 1))
    _ = 2 ^ ((3 * d + 3) * (d + 1) + 1) := by rw [← pow_mul, pow_succ]

/-- **Savitch's theorem**: every language accepted by a nondeterministic machine using space
`f` is decided by a deterministic machine using space `O(f ^ 2)`. -/
theorem savitch {L : Set (List Bool)} {f : ℕ → ℕ} (hL : L ∈ NSPACE f) :
    L ∈ DSPACE (fun n => 16 * (f n + 1) ^ 2) := by
  intro n
  obtain ⟨M, hcard, hML⟩ := hL n
  have hA : NN M ≤ 2 ^ (f n + 1) := by
    have h1 : NN M = Fintype.card M.Cfg + 1 := by simp [NN]
    have h2 : 1 ≤ 2 ^ f n := Nat.one_le_two_pow
    have : (2 : ℕ) ^ (f n + 1) = 2 ^ f n + 2 ^ f n := by ring
    omega
  refine ⟨savDSM M (f n + 1), ?_, ?_⟩
  · have h1 : Fintype.card (savDSM M (f n + 1)).Cfg = Fintype.card (SavCfg M (f n + 1)) := rfl
    rw [h1]
    calc Fintype.card (SavCfg M (f n + 1))
        ≤ 2 ^ ((3 * (f n + 1) + 3) * ((f n + 1) + 1) + 1) := card_savCfg_le M (f n + 1) hA
      _ ≤ 2 ^ (16 * (f n + 1) ^ 2) := by
          refine Nat.pow_le_pow_right (by norm_num) ?_
          nlinarith [sq_nonneg (f n)]
  · intro x hx
    refine ⟨RkB (M.E' x) (f n + 1) (some M.start) none, sav_outputs M (f n + 1) x, ?_⟩
    rw [RkB_iff_accepts M (f n + 1) hA x]
    exact (hML x hx).symm

end SavitchMain

end CS


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

