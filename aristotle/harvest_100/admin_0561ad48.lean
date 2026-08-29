/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a module docstring: Lean 4 requires `import` lines to come
first, so the very first comment of the file cannot be a module docstring.)

This file develops space bounded machines, proves Savitch's theorem
`NSPACE f ⊆ DSPACE (f ^ 2)` and deduces `PSPACE = NPSPACE`.
-/

set_option autoImplicit false

namespace CS

/-! ## Languages -/

/-- A language is a predicate on binary strings. -/
abbrev Language := List Bool → Prop

/-- The bit of `x` at position `i` (`false` beyond the end of `x`). -/
def bitAt (x : List Bool) (i : ℕ) : Bool := x.getD i false

/-! ## Bounded reachability in a directed graph on `ℕ` -/

/-- `Steps E m u v` says that `v` is reachable from `u` using at most `m` `E`-edges. -/
def Steps (E : ℕ → ℕ → Prop) : ℕ → ℕ → ℕ → Prop
  | 0, u, v => u = v
  | (m + 1), u, v => Steps E m u v ∨ ∃ w, Steps E m u w ∧ E w v

variable {E : ℕ → ℕ → Prop}

theorem Steps_zero {u v : ℕ} : Steps E 0 u v ↔ u = v := Iff.rfl

theorem Steps_succ {m u v : ℕ} :
    Steps E (m + 1) u v ↔ (Steps E m u v ∨ ∃ w, Steps E m u w ∧ E w v) := Iff.rfl

theorem Steps_refl (m u : ℕ) : Steps E m u u := by
  induction m with
  | zero => rfl
  | succ m ih => exact Or.inl ih

theorem Steps_mono {m m' u v : ℕ} (h : m ≤ m') (hs : Steps E m u v) : Steps E m' u v := by
  induction m' with
  | zero => exact (Nat.le_zero.mp h) ▸ hs
  | succ m' ih =>
    rcases Nat.lt_or_ge m (m' + 1) with h' | h'
    · exact Or.inl (ih (by omega))
    · have hm : m = m' + 1 := by omega
      exact hm ▸ hs

theorem Steps_add {a b u v : ℕ} :
    Steps E (a + b) u v ↔ ∃ w, Steps E a u w ∧ Steps E b w v := by
  induction b generalizing v with
  | zero => simp [Steps]
  | succ b ih =>
    constructor
    · rintro (h | ⟨z, hz, hzv⟩)
      · obtain ⟨w, hw1, hw2⟩ := ih.1 h
        exact ⟨w, hw1, Or.inl hw2⟩
      · obtain ⟨w, hw1, hw2⟩ := ih.1 hz
        exact ⟨w, hw1, Or.inr ⟨z, hw2, hzv⟩⟩
    · rintro ⟨w, hw1, (h2 | ⟨z, hz1, hz2⟩)⟩
      · exact Or.inl (ih.2 ⟨w, hw1, h2⟩)
      · exact Or.inr ⟨z, ih.2 ⟨w, hw1, hz1⟩, hz2⟩

theorem Steps_prop_of_edge {P : ℕ → Prop} (hE : ∀ a b, E a b → P b) {m u v : ℕ}
    (hu : P u) (h : Steps E m u v) : P v := by
  induction m generalizing v with
  | zero => exact h ▸ hu
  | succ m ih =>
    rcases h with h | ⟨w, _, hw⟩
    · exact ih h
    · exact hE _ _ hw

theorem Steps_le_of_edge {N : ℕ} (hE : ∀ a b, E a b → b ≤ N) {m u v : ℕ}
    (hu : u ≤ N) (h : Steps E m u v) : v ≤ N :=
  Steps_prop_of_edge hE hu h

theorem Steps_mono_rel {E' : ℕ → ℕ → Prop} (hEE : ∀ a b, E a b → E' a b) {m u v : ℕ}
    (h : Steps E m u v) : Steps E' m u v := by
  induction m generalizing v with
  | zero => exact h
  | succ m ih =>
    rcases h with h | ⟨w, hw, hwv⟩
    · exact Or.inl (ih h)
    · exact Or.inr ⟨w, ih hw, hEE _ _ hwv⟩

theorem reflTransGen_iff_steps {u v : ℕ} :
    Relation.ReflTransGen E u v ↔ ∃ m, Steps E m u v := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail hab hbc ih =>
      obtain ⟨m, hm⟩ := ih
      exact ⟨m + 1, Or.inr ⟨_, hm, hbc⟩⟩
  · rintro ⟨m, hm⟩
    induction m generalizing v with
    | zero => exact hm ▸ Relation.ReflTransGen.refl
    | succ m ih =>
      rcases hm with h | ⟨w, hw, hwv⟩
      · exact ih h
      · exact (ih hw).tail hwv

/-- Saturation: in a graph whose edges land in `{0,…,N}`, any reachability is witnessed by a
walk of length at most `N + 1`. -/
theorem Steps_saturate {N : ℕ} (hE : ∀ a b, E a b → b ≤ N) {m u v : ℕ} (hu : u ≤ N)
    (h : Steps E m u v) : Steps E (N + 1) u v := by
  classical
  set S : ℕ → Finset ℕ := fun i => (Finset.range (N + 1)).filter (fun w => Steps E i u w)
    with hS
  have hmem : ∀ i w, w ∈ S i ↔ Steps E i u w := by
    intro i w
    simp only [hS, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    intro hw
    exact Nat.lt_succ_of_le (Steps_le_of_edge hE hu hw)
  have hmono : ∀ i j, i ≤ j → S i ⊆ S j := by
    intro i j hij w hw
    exact (hmem j w).2 (Steps_mono hij ((hmem i w).1 hw))
  have hstab : ∀ i, S (i + 1) = S i → ∀ j, i ≤ j → S j = S i := by
    intro i hi j hij
    induction j with
    | zero =>
      have : i = 0 := by omega
      rw [this]
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · have hji : S j = S i := ih (by omega)
        apply Finset.ext
        intro w
        rw [hmem, ← hi, hmem]
        constructor
        · rintro (h1 | ⟨z, hz1, hz2⟩)
          · exact Or.inl (((hmem i w).1 (hji ▸ (hmem j w).2 h1)))
          · exact Or.inr ⟨z, ((hmem i z).1 (hji ▸ (hmem j z).2 hz1)), hz2⟩
        · rintro (h1 | ⟨z, hz1, hz2⟩)
          · exact Or.inl ((hmem j w).1 (hji ▸ (hmem i w).2 h1))
          · exact Or.inr ⟨z, (hmem j z).1 (hji ▸ (hmem i z).2 hz1), hz2⟩
      · have : i = j + 1 := by omega
        rw [this]
  have hcard : ∀ i, (S i).card ≤ N + 1 := by
    intro i
    calc (S i).card ≤ (Finset.range (N + 1)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = N + 1 := Finset.card_range _
  have hgrow : ∀ j, (∀ i, i < j → S (i + 1) ≠ S i) → j + 1 ≤ (S j).card := by
    intro j
    induction j with
    | zero =>
      intro _
      have : u ∈ S 0 := (hmem 0 u).2 rfl
      exact Finset.card_pos.2 ⟨u, this⟩
    | succ j ih =>
      intro hne
      have h1 : j + 1 ≤ (S j).card := ih (fun i hi => hne i (by omega))
      have h2 : S j ⊂ S (j + 1) :=
        ssubset_iff_subset_ne.2 ⟨hmono j (j + 1) (by omega), fun hh => hne j (by omega) hh.symm⟩
      have := Finset.card_lt_card h2
      omega
  have hex : ∃ i, i ≤ N ∧ S (i + 1) = S i := by
    by_contra hcon
    push_neg at hcon
    have := hgrow (N + 1) (fun i hi => hcon i (by omega))
    have := hcard (N + 1)
    omega
  obtain ⟨i, hiN, hi⟩ := hex
  have hvm : v ∈ S (max m i) := hmono m (max m i) (le_max_left _ _) ((hmem m v).2 h)
  rw [hstab i hi (max m i) (le_max_right _ _)] at hvm
  exact Steps_mono (by omega) ((hmem i v).1 hvm)

/-! ## Machine models

Both models are *random access input* space bounded machines: a configuration determines a
position of the input that is read, and the transition depends on the configuration together
with the bit read there.  This is what makes the classes non-trivial: a machine has no other
access to its input (see `CS.firstBit_mem_dspace` for a concrete language in `DSPACE 0`).

The transition data is allowed to depend arbitrarily on the input length `n`, so the model is
non-uniform; Savitch's simulation below is proved in this generality, and in particular applies
to uniform machines. -/

/-- A nondeterministic space bounded machine.  Configurations for inputs of length `n` are the
naturals `< size n`. -/
structure NMachine where
  /-- number of configurations on inputs of length `n` -/
  size : ℕ → ℕ
  /-- initial configuration -/
  init : ℕ → ℕ
  /-- input position read by a configuration -/
  ipos : ℕ → ℕ → ℕ
  /-- transition relation, depending on the bit read -/
  step : ℕ → Bool → ℕ → ℕ → Prop
  /-- accepting configurations -/
  acc : ℕ → ℕ → Prop
  init_lt : ∀ n, init n < size n
  step_lt : ∀ n b u v, step n b u v → u < size n ∧ v < size n

/-- The configuration graph of `M` on input `x`. -/
def NMachine.edge (M : NMachine) (x : List Bool) (u v : ℕ) : Prop :=
  M.step x.length (bitAt x (M.ipos x.length u)) u v

/-- `M` accepts `x` if some accepting configuration is reachable from the initial one. -/
def NMachine.Accepts (M : NMachine) (x : List Bool) : Prop :=
  ∃ v, Relation.ReflTransGen (M.edge x) (M.init x.length) v ∧ M.acc x.length v

/-- `M` uses space `s`, i.e. at most `2 ^ s n` configurations on inputs of length `n`. -/
def NMachine.SpaceBounded (M : NMachine) (s : ℕ → ℕ) : Prop := ∀ n, M.size n ≤ 2 ^ s n

/-- A deterministic space bounded machine. -/
structure DMachine where
  /-- configuration space on inputs of length `n` -/
  Conf : ℕ → Type
  /-- initial configuration -/
  init : (n : ℕ) → Conf n
  /-- input position read by a configuration -/
  ipos : (n : ℕ) → Conf n → ℕ
  /-- transition function, depending on the bit read -/
  step : (n : ℕ) → Bool → Conf n → Conf n
  /-- accepting configurations -/
  acc : (n : ℕ) → Conf n → Prop

/-- One step of `M` on input `x`. -/
def DMachine.next (M : DMachine) (x : List Bool) (c : M.Conf x.length) : M.Conf x.length :=
  M.step x.length (bitAt x (M.ipos x.length c)) c

/-- `M` accepts `x` if its (unique) run reaches an accepting configuration. -/
def DMachine.Accepts (M : DMachine) (x : List Bool) : Prop :=
  ∃ t, M.acc x.length ((M.next x)^[t] (M.init x.length))

/-- `M` uses space `s`: its configuration space embeds into `2 ^ s n` values. -/
def DMachine.SpaceBounded (M : DMachine) (s : ℕ → ℕ) : Prop :=
  ∀ n, Nonempty (M.Conf n ↪ Fin (2 ^ s n))

/-- `NSPACE f`: languages recognised by a nondeterministic machine in space `O(f)`. -/
def NSPACE (f : ℕ → ℕ) : Set Language :=
  {L | ∃ M : NMachine, ∃ c : ℕ,
      M.SpaceBounded (fun n => c * (f n + 1)) ∧ ∀ x, L x ↔ M.Accepts x}

/-- `DSPACE f`: languages decided by a deterministic machine in space `O(f)`. -/
def DSPACE (f : ℕ → ℕ) : Set Language :=
  {L | ∃ M : DMachine, ∃ c : ℕ,
      M.SpaceBounded (fun n => c * (f n + 1)) ∧ ∀ x, L x ↔ M.Accepts x}

/-! ## The Savitch simulator

The deterministic simulator is a stack machine implementing the usual recursive
`REACH(u, v, k)` procedure: `u` reaches `v` in at most `2 ^ k` steps iff there is a midpoint
`w` with `REACH(u, w, k-1)` and `REACH(w, v, k-1)`. -/

/-- A stack frame `⟨u, v, k, m, ph⟩`: we are computing `REACH(u,v,k)`, currently trying the
midpoint `m`, in phase `ph` (`false`: first recursive call, `true`: second one). -/
@[ext]
structure Frame where
  /-- source -/
  u : ℕ
  /-- target -/
  v : ℕ
  /-- level -/
  k : ℕ
  /-- current midpoint candidate -/
  m : ℕ
  /-- phase -/
  ph : Bool

/-- A configuration of the simulator: an optional returned value together with the stack. -/
abbrev SState := Option Bool × List Frame

open Classical in
/-- One step of the simulator, given the bit of the input that the state reads. -/
noncomputable def sstep (N : ℕ) (edge : Bool → ℕ → ℕ → Prop) (b : Bool) : SState → SState
  | (r, []) => (r, [])
  | (none, F :: rest) =>
      if F.k = 0 then (some (decide (F.u = F.v ∨ edge b F.u F.v)), rest)
      else if F.m ≤ N then
        (none, ⟨F.u, F.m, F.k - 1, 0, false⟩ :: ⟨F.u, F.v, F.k, F.m, false⟩ :: rest)
      else (some false, rest)
  | (some c, F :: rest) =>
      if F.k = 0 ∨ N < F.m then (some false, rest)
      else if F.ph then
        (if c then (some true, rest) else (none, ⟨F.u, F.v, F.k, F.m + 1, false⟩ :: rest))
      else
        (if c then (none, ⟨F.m, F.v, F.k - 1, 0, false⟩ :: ⟨F.u, F.v, F.k, F.m, true⟩ :: rest)
         else (none, ⟨F.u, F.v, F.k, F.m + 1, false⟩ :: rest))

/-- The input position read by a simulator state. -/
def spos (epos : ℕ → ℕ) : SState → ℕ
  | (none, F :: _) => epos F.u
  | _ => 0

section StepEqs

variable {N : ℕ} {edge : Bool → ℕ → ℕ → Prop} {b : Bool} {F : Frame} {rest : List Frame}
  {c : Bool}

open Classical in
theorem sstep_none_zero (h : F.k = 0) :
    sstep N edge b (none, F :: rest) = (some (decide (F.u = F.v ∨ edge b F.u F.v)), rest) := by
  simp [sstep, h]

theorem sstep_none_push (hk : F.k ≠ 0) (hm : F.m ≤ N) :
    sstep N edge b (none, F :: rest)
      = (none, ⟨F.u, F.m, F.k - 1, 0, false⟩ :: ⟨F.u, F.v, F.k, F.m, false⟩ :: rest) := by
  simp [sstep, hk, hm]

theorem sstep_none_fail (hk : F.k ≠ 0) (hm : ¬ F.m ≤ N) :
    sstep N edge b (none, F :: rest) = (some false, rest) := by
  simp [sstep, hk, hm]

theorem sstep_some_bad (h : F.k = 0 ∨ N < F.m) :
    sstep N edge b (some c, F :: rest) = (some false, rest) := by
  simp [sstep, h]

theorem sstep_some_true_true (hk : F.k ≠ 0) (hm : ¬ N < F.m) (hph : F.ph = true)
    (hc : c = true) : sstep N edge b (some c, F :: rest) = (some true, rest) := by
  simp [sstep, hk, hm, hph, hc]

theorem sstep_some_true_false (hk : F.k ≠ 0) (hm : ¬ N < F.m) (hph : F.ph = true)
    (hc : c = false) :
    sstep N edge b (some c, F :: rest) = (none, ⟨F.u, F.v, F.k, F.m + 1, false⟩ :: rest) := by
  simp [sstep, hk, hm, hph, hc]

theorem sstep_some_false_true (hk : F.k ≠ 0) (hm : ¬ N < F.m) (hph : F.ph = false)
    (hc : c = true) :
    sstep N edge b (some c, F :: rest)
      = (none, ⟨F.m, F.v, F.k - 1, 0, false⟩ :: ⟨F.u, F.v, F.k, F.m, true⟩ :: rest) := by
  simp [sstep, hk, hm, hph, hc]

theorem sstep_some_false_false (hk : F.k ≠ 0) (hm : ¬ N < F.m) (hph : F.ph = false)
    (hc : c = false) :
    sstep N edge b (some c, F :: rest) = (none, ⟨F.u, F.v, F.k, F.m + 1, false⟩ :: rest) := by
  simp [sstep, hk, hm, hph, hc]

end StepEqs

/-- The graph explored by the simulator, once the input bits are fixed. -/
def edgeOf (edge : Bool → ℕ → ℕ → Prop) (epos : ℕ → ℕ) (bitf : ℕ → Bool) : ℕ → ℕ → Prop :=
  fun u v => edge (bitf (epos u)) u v

/-- One step of the simulator on a fixed input. -/
noncomputable def srun (N : ℕ) (edge : Bool → ℕ → ℕ → Prop) (epos : ℕ → ℕ) (bitf : ℕ → Bool) :
    SState → SState := fun s => sstep N edge (bitf (spos epos s)) s

section Simulator

variable {N : ℕ} {edge : Bool → ℕ → ℕ → Prop} {epos : ℕ → ℕ} {bitf : ℕ → Bool}

/-- States with an empty stack are fixed points. -/
theorem srun_nil (r : Option Bool) : srun N edge epos bitf (r, []) = (r, []) := by
  simp [srun, sstep]

theorem srun_iterate_nil (r : Option Bool) (t : ℕ) :
    (srun N edge epos bitf)^[t] (r, []) = (r, []) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, srun_nil, ih]

open Classical in
theorem srun_none_zero' {F : Frame} {rest : List Frame} (h : F.k = 0) :
    srun N edge epos bitf (none, F :: rest)
      = (some (decide (F.u = F.v ∨ edgeOf edge epos bitf F.u F.v)), rest) :=
  sstep_none_zero h

theorem srun_none_push' {F : Frame} {rest : List Frame} (hk : F.k ≠ 0) (hm : F.m ≤ N) :
    srun N edge epos bitf (none, F :: rest)
      = (none, ⟨F.u, F.m, F.k - 1, 0, false⟩ :: ⟨F.u, F.v, F.k, F.m, false⟩ :: rest) :=
  sstep_none_push hk hm

theorem srun_none_fail' {F : Frame} {rest : List Frame} (hk : F.k ≠ 0) (hm : ¬ F.m ≤ N) :
    srun N edge epos bitf (none, F :: rest) = (some false, rest) :=
  sstep_none_fail hk hm

theorem srun_some_true_true' {c : Bool} {F : Frame} {rest : List Frame} (hk : F.k ≠ 0)
    (hm : ¬ N < F.m) (hph : F.ph = true) (hc : c = true) :
    srun N edge epos bitf (some c, F :: rest) = (some true, rest) :=
  sstep_some_true_true hk hm hph hc

theorem srun_some_true_false' {c : Bool} {F : Frame} {rest : List Frame} (hk : F.k ≠ 0)
    (hm : ¬ N < F.m) (hph : F.ph = true) (hc : c = false) :
    srun N edge epos bitf (some c, F :: rest)
      = (none, ⟨F.u, F.v, F.k, F.m + 1, false⟩ :: rest) :=
  sstep_some_true_false hk hm hph hc

theorem srun_some_false_true' {c : Bool} {F : Frame} {rest : List Frame} (hk : F.k ≠ 0)
    (hm : ¬ N < F.m) (hph : F.ph = false) (hc : c = true) :
    srun N edge epos bitf (some c, F :: rest)
      = (none, ⟨F.m, F.v, F.k - 1, 0, false⟩ :: ⟨F.u, F.v, F.k, F.m, true⟩ :: rest) :=
  sstep_some_false_true hk hm hph hc

theorem srun_some_false_false' {c : Bool} {F : Frame} {rest : List Frame} (hk : F.k ≠ 0)
    (hm : ¬ N < F.m) (hph : F.ph = false) (hc : c = false) :
    srun N edge epos bitf (some c, F :: rest)
      = (none, ⟨F.u, F.v, F.k, F.m + 1, false⟩ :: rest) :=
  sstep_some_false_false hk hm hph hc

/-- Reachability between simulator states is transitive. -/
theorem srun_trans {a b c : SState} (h1 : ∃ t, (srun N edge epos bitf)^[t] a = b)
    (h2 : ∃ t, (srun N edge epos bitf)^[t] b = c) : ∃ t, (srun N edge epos bitf)^[t] a = c := by
  obtain ⟨t1, rfl⟩ := h1
  obtain ⟨t2, rfl⟩ := h2
  exact ⟨t2 + t1, by rw [Function.iterate_add_apply]⟩

theorem srun_step_reach {a b : SState} (h : srun N edge epos bitf a = b) :
    ∃ t, (srun N edge epos bitf)^[t] a = b :=
  ⟨1, by rw [Function.iterate_one]; exact h⟩

open Classical in
/-- Main correctness lemma for the simulator: a call frame at level `k` returns the truth value
of `Steps (2 ^ k) u v`. -/
theorem sim_key (hE : ∀ u v, edgeOf edge epos bitf u v → u ≤ N ∧ v ≤ N) :
    ∀ (k u v : ℕ) (rest : List Frame), u ≤ N → v ≤ N →
      ∃ t, (srun N edge epos bitf)^[t] (none, ⟨u, v, k, 0, false⟩ :: rest)
        = (some (decide (Steps (edgeOf edge epos bitf) (2 ^ k) u v)), rest) := by
  have hdec : ∀ (P Q : Prop) (i1 : Decidable P) (i2 : Decidable Q) (rest : List Frame), (P ↔ Q) →
      ((some (@decide P i1), rest) : SState) = (some (@decide Q i2), rest) := by
    intro P Q i1 i2 rest h
    rw [(@decide_eq_decide P Q i1 i2).2 h]
  intro k
  induction k with
  | zero =>
    intro u v rest hu hv
    refine ⟨1, ?_⟩
    rw [Function.iterate_one, srun_none_zero' rfl]
    refine hdec _ _ _ _ _ ?_
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨u, rfl, h⟩
    · rintro (h | ⟨w, hw, hwv⟩)
      · exact Or.inl h
      · exact Or.inr (hw ▸ hwv)
  | succ k ih =>
    have hshift : ∀ (m u v : ℕ),
        ¬ (Steps (edgeOf edge epos bitf) (2 ^ k) u m ∧ Steps (edgeOf edge epos bitf) (2 ^ k) m v) →
        ((∃ w, m + 1 ≤ w ∧ w ≤ N ∧ Steps (edgeOf edge epos bitf) (2 ^ k) u w ∧
            Steps (edgeOf edge epos bitf) (2 ^ k) w v) ↔
          (∃ w, m ≤ w ∧ w ≤ N ∧ Steps (edgeOf edge epos bitf) (2 ^ k) u w ∧
            Steps (edgeOf edge epos bitf) (2 ^ k) w v)) := by
      intro m u v hbad
      constructor
      · rintro ⟨w, h1, h2, h3, h4⟩
        exact ⟨w, by omega, h2, h3, h4⟩
      · rintro ⟨w, h1, h2, h3, h4⟩
        rcases eq_or_lt_of_le h1 with heq | hlt
        · exact absurd ⟨heq ▸ h3, heq ▸ h4⟩ hbad
        · exact ⟨w, hlt, h2, h3, h4⟩
    have loop : ∀ (d m u v : ℕ) (rest : List Frame), N + 1 ≤ m + d → u ≤ N → v ≤ N →
        ∃ t, (srun N edge epos bitf)^[t] (none, ⟨u, v, k + 1, m, false⟩ :: rest)
          = (some (decide (∃ w, m ≤ w ∧ w ≤ N ∧
              Steps (edgeOf edge epos bitf) (2 ^ k) u w ∧
              Steps (edgeOf edge epos bitf) (2 ^ k) w v)), rest) := by
      intro d
      induction d with
      | zero =>
        intro m u v rest hd hu hv
        have hno : ¬ ∃ w, m ≤ w ∧ w ≤ N ∧ Steps (edgeOf edge epos bitf) (2 ^ k) u w ∧
            Steps (edgeOf edge epos bitf) (2 ^ k) w v := by
          rintro ⟨w, h1, h2, -, -⟩
          omega
        refine ⟨1, ?_⟩
        rw [Function.iterate_one, decide_eq_false hno]
        exact srun_none_fail' (by show k + 1 ≠ 0; omega) (by show ¬ m ≤ N; omega)
      | succ d ihd =>
        intro m u v rest hd hu hv
        by_cases hm : m ≤ N
        · have e1 : srun N edge epos bitf (none, (⟨u, v, k + 1, m, false⟩ : Frame) :: rest)
              = (none, (⟨u, m, k, 0, false⟩ : Frame) ::
                  (⟨u, v, k + 1, m, false⟩ : Frame) :: rest) :=
            srun_none_push' (by show k + 1 ≠ 0; omega) (show m ≤ N from hm)
          refine srun_trans (srun_step_reach e1) ?_
          refine srun_trans (ih u m ((⟨u, v, k + 1, m, false⟩ : Frame) :: rest) hu hm) ?_
          by_cases hum : Steps (edgeOf edge epos bitf) (2 ^ k) u m
          · rw [decide_eq_true hum]
            have e2 : srun N edge epos bitf
                (some true, (⟨u, v, k + 1, m, false⟩ : Frame) :: rest)
                = (none, (⟨m, v, k, 0, false⟩ : Frame) ::
                    (⟨u, v, k + 1, m, true⟩ : Frame) :: rest) :=
              srun_some_false_true' (by show k + 1 ≠ 0; omega) (by show ¬ N < m; omega) rfl rfl
            refine srun_trans (srun_step_reach e2) ?_
            refine srun_trans (ih m v ((⟨u, v, k + 1, m, true⟩ : Frame) :: rest) hm hv) ?_
            by_cases hmv : Steps (edgeOf edge epos bitf) (2 ^ k) m v
            · rw [decide_eq_true hmv]
              have hP : ∃ w, m ≤ w ∧ w ≤ N ∧ Steps (edgeOf edge epos bitf) (2 ^ k) u w ∧
                  Steps (edgeOf edge epos bitf) (2 ^ k) w v := ⟨m, le_rfl, hm, hum, hmv⟩
              rw [decide_eq_true hP]
              refine ⟨1, ?_⟩
              rw [Function.iterate_one]
              exact srun_some_true_true' (by show k + 1 ≠ 0; omega) (by show ¬ N < m; omega)
                rfl rfl
            · rw [decide_eq_false hmv]
              have e3 : srun N edge epos bitf
                  (some false, (⟨u, v, k + 1, m, true⟩ : Frame) :: rest)
                  = (none, (⟨u, v, k + 1, m + 1, false⟩ : Frame) :: rest) :=
                srun_some_true_false' (by show k + 1 ≠ 0; omega) (by show ¬ N < m; omega) rfl rfl
              refine srun_trans (srun_step_reach e3) ?_
              refine srun_trans (ihd (m + 1) u v rest (by omega) hu hv) ?_
              exact ⟨0, hdec _ _ _ _ _ (hshift m u v (fun h => hmv h.2))⟩
          · rw [decide_eq_false hum]
            have e3 : srun N edge epos bitf
                (some false, (⟨u, v, k + 1, m, false⟩ : Frame) :: rest)
                = (none, (⟨u, v, k + 1, m + 1, false⟩ : Frame) :: rest) :=
              srun_some_false_false' (by show k + 1 ≠ 0; omega) (by show ¬ N < m; omega) rfl rfl
            refine srun_trans (srun_step_reach e3) ?_
            refine srun_trans (ihd (m + 1) u v rest (by omega) hu hv) ?_
            exact ⟨0, hdec _ _ _ _ _ (hshift m u v (fun h => hum h.1))⟩
        · have hno : ¬ ∃ w, m ≤ w ∧ w ≤ N ∧ Steps (edgeOf edge epos bitf) (2 ^ k) u w ∧
              Steps (edgeOf edge epos bitf) (2 ^ k) w v := by
            rintro ⟨w, h1, h2, -, -⟩
            omega
          refine ⟨1, ?_⟩
          rw [Function.iterate_one, decide_eq_false hno]
          exact srun_none_fail' (by show k + 1 ≠ 0; omega) (by show ¬ m ≤ N; omega)
    intro u v rest hu hv
    obtain ⟨t, ht⟩ := loop (N + 1) 0 u v rest (by omega) hu hv
    refine ⟨t, ?_⟩
    rw [ht]
    refine hdec _ _ _ _ _ ?_
    constructor
    · rintro ⟨w, -, -, h1, h2⟩
      have : (2:ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
      rw [this]
      exact Steps_add.2 ⟨w, h1, h2⟩
    · intro h
      have hpow : (2:ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
      rw [hpow] at h
      obtain ⟨w, h1, h2⟩ := Steps_add.1 h
      have hwN : w ≤ N := Steps_le_of_edge (fun a b hab => (hE a b hab).2) hu h1
      exact ⟨w, Nat.zero_le _, hwN, h1, h2⟩

/-- The simulator, started on the top level call `REACH(u, tgt, K)`, accepts iff `tgt` is
reachable from `u` in at most `2 ^ K` steps. -/
theorem sim_accepts (hE : ∀ u v, edgeOf edge epos bitf u v → u ≤ N ∧ v ≤ N)
    (u tgt K : ℕ) (hu : u ≤ N) (htgt : tgt ≤ N) :
    (∃ t, (srun N edge epos bitf)^[t] (none, [⟨u, tgt, K, 0, false⟩]) = (some true, []))
      ↔ Steps (edgeOf edge epos bitf) (2 ^ K) u tgt := by
  classical
  obtain ⟨T, hT⟩ := sim_key hE K u tgt [] hu htgt
  constructor
  · rintro ⟨t, ht⟩
    have h1 : (srun N edge epos bitf)^[max t T] (none, [⟨u, tgt, K, 0, false⟩])
        = (some true, []) := by
      rw [show max t T = (max t T - t) + t by omega, Function.iterate_add_apply, ht,
        srun_iterate_nil]
    have h2 : (srun N edge epos bitf)^[max t T] (none, [⟨u, tgt, K, 0, false⟩])
        = (some (decide (Steps (edgeOf edge epos bitf) (2 ^ K) u tgt)), []) := by
      rw [show max t T = (max t T - T) + T by omega, Function.iterate_add_apply, hT,
        srun_iterate_nil]
    rw [h1] at h2
    have h3 : (true : Bool) = decide (Steps (edgeOf edge epos bitf) (2 ^ K) u tgt) := by
      simpa using congrArg Prod.fst h2
    exact of_decide_eq_true h3.symm
  · intro hS
    exact ⟨T, by rwa [decide_eq_true hS] at hT⟩

end Simulator

/-! ## Validity of simulator states, and counting them -/

/-- A frame is well formed for parameters `N`, `K`. -/
structure FrameOk (N K : ℕ) (F : Frame) : Prop where
  /-- level bound -/
  hk : F.k ≤ K
  /-- source bound -/
  hu : F.u ≤ N
  /-- target bound -/
  hv : F.v ≤ N
  /-- midpoint bound -/
  hm : F.m ≤ N + 1

/-- A simulator state is valid if its stack is well formed: levels increase by one from top to
bottom and all components are in range. -/
def SValid (N K : ℕ) (p : SState) : Prop :=
  List.IsChain (fun a b : Frame => b.k = a.k + 1) p.2 ∧ ∀ F ∈ p.2, FrameOk N K F

/-- Replacing the top frame by one with the same level preserves the chain condition. -/
theorem isChain_cons_replace {F G : Frame} {rest : List Frame} (hk : G.k = F.k)
    (h : List.IsChain (fun a b : Frame => b.k = a.k + 1) (F :: rest)) :
    List.IsChain (fun a b : Frame => b.k = a.k + 1) (G :: rest) := by
  rw [List.isChain_cons] at h ⊢
  exact ⟨fun y hy => by rw [hk]; exact h.1 y hy, h.2⟩

/-- Pushing a frame one level below the current top preserves the chain condition. -/
theorem isChain_push {A G : Frame} {rest : List Frame} (hA : G.k = A.k + 1)
    (h : List.IsChain (fun a b : Frame => b.k = a.k + 1) (G :: rest)) :
    List.IsChain (fun a b : Frame => b.k = a.k + 1) (A :: G :: rest) := by
  rw [List.isChain_cons]
  refine ⟨?_, h⟩
  intro y hy
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
  exact hy ▸ hA

theorem chain_length_aux {K : ℕ} : ∀ (l : List Frame) (F : Frame),
    List.IsChain (fun a b : Frame => b.k = a.k + 1) (F :: l) → (∀ G ∈ F :: l, G.k ≤ K) →
      (F :: l).length + F.k ≤ K + 1 := by
  intro l
  induction l with
  | nil =>
    intro F _ hall
    have := hall F (by simp)
    simp
    omega
  | cons G l ih =>
    intro F hchain hall
    rw [List.isChain_cons] at hchain
    have hGk : G.k = F.k + 1 := hchain.1 G (by simp)
    have := ih G hchain.2 (fun H hH => hall H (List.mem_cons_of_mem _ hH))
    simp only [List.length_cons] at this ⊢
    omega

theorem SValid.length_le {N K : ℕ} {p : SState} (h : SValid N K p) : p.2.length ≤ K + 1 := by
  obtain ⟨r, l⟩ := p
  obtain ⟨hchain, hall⟩ := h
  cases l with
  | nil => simp
  | cons F rest =>
    have := chain_length_aux (K := K) rest F hchain (fun G hG => (hall G hG).hk)
    simp only [List.length_cons] at this ⊢
    omega

theorem sstep_valid {N K : ℕ} (edge : Bool → ℕ → ℕ → Prop) (b : Bool) {p : SState}
    (h : SValid N K p) : SValid N K (sstep N edge b p) := by
  obtain ⟨r, l⟩ := p
  cases l with
  | nil => exact h
  | cons F rest =>
    obtain ⟨hchain, hall⟩ := h
    have hrest : List.IsChain (fun a b : Frame => b.k = a.k + 1) rest :=
      (List.isChain_cons.1 hchain).2
    have hallrest : ∀ G ∈ rest, FrameOk N K G := fun G hG => hall G (List.mem_cons_of_mem _ hG)
    have hF : FrameOk N K F := hall F (by simp)
    have hFk := hF.hk
    have hFu := hF.hu
    have hFv := hF.hv
    have hFm := hF.hm
    have hpop : ∀ r' : Option Bool, SValid N K ((r', rest) : SState) :=
      fun _ => ⟨hrest, hallrest⟩
    have hpush : ∀ A B : Frame, B.k = F.k → A.k + 1 = B.k → FrameOk N K A → FrameOk N K B →
        SValid N K ((none, A :: B :: rest) : SState) := by
      intro A B hB hA hAok hBok
      refine ⟨isChain_push (by omega) (isChain_cons_replace hB hchain), ?_⟩
      intro G hG
      simp only [List.mem_cons] at hG
      rcases hG with rfl | rfl | hG
      · exact hAok
      · exact hBok
      · exact hallrest G hG
    have hrepl : ∀ C : Frame, C.k = F.k → FrameOk N K C →
        SValid N K ((none, C :: rest) : SState) := by
      intro C hC hCok
      refine ⟨isChain_cons_replace hC hchain, ?_⟩
      intro G hG
      simp only [List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact hCok
      · exact hallrest G hG
    cases r with
    | none =>
      by_cases hk : F.k = 0
      · rw [sstep_none_zero hk]
        exact hpop _
      · by_cases hm : F.m ≤ N
        · rw [sstep_none_push hk hm]
          exact hpush _ _ rfl (show F.k - 1 + 1 = F.k by omega)
            ⟨show F.k - 1 ≤ K by omega, hFu, hm, Nat.zero_le _⟩ ⟨hFk, hFu, hFv, hFm⟩
        · rw [sstep_none_fail hk hm]
          exact hpop _
    | some c =>
      by_cases hbad : F.k = 0 ∨ N < F.m
      · rw [sstep_some_bad hbad]
        exact hpop _
      · push_neg at hbad
        obtain ⟨hk, hm⟩ := hbad
        have hm' : ¬ N < F.m := by omega
        cases hph : F.ph
        · cases hc : c
          · rw [sstep_some_false_false hk hm' hph rfl]
            exact hrepl _ rfl ⟨hFk, hFu, hFv, show F.m + 1 ≤ N + 1 by omega⟩
          · rw [sstep_some_false_true hk hm' hph rfl]
            exact hpush _ _ rfl (show F.k - 1 + 1 = F.k by omega)
              ⟨show F.k - 1 ≤ K by omega, hm, hFv, Nat.zero_le _⟩ ⟨hFk, hFu, hFv, hFm⟩
        · cases hc : c
          · rw [sstep_some_true_false hk hm' hph rfl]
            exact hrepl _ rfl ⟨hFk, hFu, hFv, show F.m + 1 ≤ N + 1 by omega⟩
          · rw [sstep_some_true_true hk hm' hph rfl]
            exact hpop _

/-- The number of frames occurring in valid states. -/
abbrev FrameCode (N K : ℕ) : Type := Fin (N + 1) × Fin (N + 1) × Fin (K + 1) × Fin (N + 2) × Bool

/-- Encoding of a frame; injective on well formed frames. -/
def fcode (N K : ℕ) (F : Frame) : FrameCode N K :=
  (⟨min F.u N, by omega⟩, ⟨min F.v N, by omega⟩, ⟨min F.k K, by omega⟩,
    ⟨min F.m (N + 1), by omega⟩, F.ph)

theorem fcode_inj {N K : ℕ} {F G : Frame} (hF : FrameOk N K F) (hG : FrameOk N K G)
    (h : fcode N K F = fcode N K G) : F = G := by
  obtain ⟨hFk, hFu, hFv, hFm⟩ := hF
  obtain ⟨hGk, hGu, hGv, hGm⟩ := hG
  simp only [fcode, Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact Frame.ext (by omega) (by omega) (by omega) (by omega) h5

/-- The arithmetic bound behind the space bound of the simulator. -/
theorem svalid_card_bound {N K s : ℕ} (hN : N ≤ 2 ^ s) (hK : K = s + 1) :
    3 * ((N + 1) * ((N + 1) * ((K + 1) * ((N + 2) * 2))) + 1) ^ (K + 1)
      ≤ 2 ^ (6 * (s + 2) ^ 2) := by
  have hp : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
  have h1 : N + 1 ≤ 2 ^ (s + 1) := by
    have : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by rw [pow_succ]; ring
    omega
  have h2 : N + 2 ≤ 2 ^ (s + 2) := by
    have : 2 ^ (s + 2) = 2 ^ s + 2 ^ s + 2 ^ s + 2 ^ s := by rw [pow_succ, pow_succ]; ring
    omega
  have h3 : K + 1 ≤ 2 ^ (s + 2) := by
    rw [hK]
    exact le_of_lt Nat.lt_two_pow_self
  have hM : (N + 1) * ((N + 1) * ((K + 1) * ((N + 2) * 2))) ≤ 2 ^ (4 * s + 7) := by
    have : (2:ℕ) ^ (s+1) * (2 ^ (s+1) * (2 ^ (s+2) * (2 ^ (s+2) * 2))) = 2 ^ (4 * s + 7) := by
      rw [← pow_succ, ← pow_add, ← pow_add, ← pow_add]
      ring_nf
    calc (N + 1) * ((N + 1) * ((K + 1) * ((N + 2) * 2)))
        ≤ 2 ^ (s+1) * (2 ^ (s+1) * (2 ^ (s+2) * (2 ^ (s+2) * 2))) := by
          gcongr
      _ = 2 ^ (4 * s + 7) := this
  have hM1 : (N + 1) * ((N + 1) * ((K + 1) * ((N + 2) * 2))) + 1 ≤ 2 ^ (4 * s + 8) := by
    have hq : (1 : ℕ) ≤ 2 ^ (4 * s + 7) := Nat.one_le_two_pow
    have : 2 ^ (4 * s + 8) = 2 ^ (4 * s + 7) + 2 ^ (4 * s + 7) := by rw [pow_succ]; ring
    omega
  calc 3 * ((N + 1) * ((N + 1) * ((K + 1) * ((N + 2) * 2))) + 1) ^ (K + 1)
      ≤ 2 ^ 2 * (2 ^ (4 * s + 8)) ^ (K + 1) := by
        gcongr
        · norm_num
    _ = 2 ^ (2 + (4 * s + 8) * (s + 2)) := by
        rw [← pow_mul, ← pow_add, hK]
    _ ≤ 2 ^ (6 * (s + 2) ^ 2) := by
        apply Nat.pow_le_pow_right (by norm_num)
        nlinarith [sq_nonneg s]

/-- There are at most `2 ^ (6 * (s + 2) ^ 2)` valid states when `N ≤ 2 ^ s` and `K = s + 1`. -/
theorem svalid_small {N K s : ℕ} (hN : N ≤ 2 ^ s) (hK : K = s + 1) :
    Nonempty ({p : SState // SValid N K p} ↪ Fin (2 ^ (6 * (s + 2) ^ 2))) := by
  classical
  refine ⟨Function.Embedding.trans (Function.Embedding.trans
    (⟨fun p => (p.1.1, fun i : Fin (K + 1) => (p.1.2[(i : ℕ)]?).map (fcode N K)), ?_⟩ :
      {p : SState // SValid N K p} ↪
        Option Bool × (Fin (K + 1) → Option (FrameCode N K)))
    (Fintype.equivFin _).toEmbedding) (Fin.castLEEmb ?_)⟩
  · intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨h1, h2'⟩ := hpq
    have h2 : ∀ i : Fin (K + 1),
        (p.1.2[(i : ℕ)]?).map (fcode N K) = (q.1.2[(i : ℕ)]?).map (fcode N K) :=
      fun i => congrFun h2' i
    refine Subtype.ext (Prod.ext h1 ?_)
    refine List.ext_getElem? ?_
    intro i
    by_cases hi : i < K + 1
    · have hi2 := h2 ⟨i, hi⟩
      simp only at hi2
      cases hp : p.1.2[i]? with
      | none =>
        cases hq : q.1.2[i]? with
        | none => rfl
        | some G => rw [hp, hq] at hi2; simp at hi2
      | some F =>
        cases hq : q.1.2[i]? with
        | none => rw [hp, hq] at hi2; simp at hi2
        | some G =>
          rw [hp, hq] at hi2
          simp only [Option.map_some, Option.some.injEq] at hi2
          have hFmem : F ∈ p.1.2 := List.mem_of_getElem? hp
          have hGmem : G ∈ q.1.2 := List.mem_of_getElem? hq
          rw [fcode_inj (p.2.2 F hFmem) (q.2.2 G hGmem) hi2]
    · have hlp : p.1.2.length ≤ i := le_trans p.2.length_le (by omega)
      have hlq : q.1.2.length ≤ i := le_trans q.2.length_le (by omega)
      rw [List.getElem?_eq_none hlp, List.getElem?_eq_none hlq]
  · have hcard : Fintype.card (Option Bool × (Fin (K + 1) → Option (FrameCode N K)))
        = 3 * ((N + 1) * ((N + 1) * ((K + 1) * ((N + 2) * 2))) + 1) ^ (K + 1) := by
      simp [FrameCode]
    rw [hcard]
    exact svalid_card_bound hN hK

/-! ## Savitch's theorem -/

/-- The configuration graph of `M` on inputs of length `n`, extended by a fresh target node
`M.size n` reachable from every accepting configuration. -/
def NMachine.edgeAll (M : NMachine) (n : ℕ) : Bool → ℕ → ℕ → Prop :=
  fun b u v => u < M.size n ∧ (if v = M.size n then M.acc n u else M.step n b u v)

theorem NMachine.edgeAll_le (M : NMachine) (n : ℕ) (epos : ℕ → ℕ) (bitf : ℕ → Bool) (u v : ℕ)
    (h : edgeOf (M.edgeAll n) epos bitf u v) : u ≤ M.size n ∧ v ≤ M.size n := by
  obtain ⟨hu, hv⟩ := h
  refine ⟨hu.le, ?_⟩
  by_cases hvN : v = M.size n
  · exact hvN.le
  · rw [if_neg hvN] at hv
    exact (M.step_lt _ _ _ _ hv).2.le

/-- Acceptance is reachability of the fresh target node. -/
theorem NMachine.accepts_iff_steps (M : NMachine) (x : List Bool) {K : ℕ}
    (hK : M.size x.length + 1 ≤ 2 ^ K) :
    M.Accepts x ↔
      Steps (edgeOf (M.edgeAll x.length) (M.ipos x.length) (bitAt x)) (2 ^ K)
        (M.init x.length) (M.size x.length) := by
  set n := x.length
  set N := M.size n with hN
  set E : ℕ → ℕ → Prop := M.edge x with hEdef
  set E' : ℕ → ℕ → Prop := edgeOf (M.edgeAll n) (M.ipos n) (bitAt x) with hE'def
  have hEE' : ∀ u v, E u v → E' u v := by
    intro u v h
    have hlt := M.step_lt n _ _ _ h
    refine ⟨hlt.1, ?_⟩
    rw [if_neg (by omega : v ≠ N)]
    exact h
  have hE'lt : ∀ u v, E' u v → u < N := fun u v h => h.1
  have hE'le : ∀ u v, E' u v → v ≤ N := fun u v h => (M.edgeAll_le n (M.ipos n) (bitAt x) u v h).2
  have hE'E : ∀ u v, v ≠ N → E' u v → E u v := by
    intro u v hv h
    have := h.2
    rwa [if_neg hv] at this
  have hRTGlt : ∀ w, Relation.ReflTransGen E (M.init n) w → w < N := by
    intro w hw
    obtain ⟨m, hm⟩ := reflTransGen_iff_steps.1 hw
    refine Steps_prop_of_edge (P := fun w => w < N) ?_ (M.init_lt n) hm
    intro a b hab
    exact (M.step_lt n _ _ _ hab).2
  have hpath : ∀ m w, Steps E' m (M.init n) w →
      (∃ v, Relation.ReflTransGen E (M.init n) v ∧ M.acc n v) ∨
        Relation.ReflTransGen E (M.init n) w := by
    intro m
    induction m with
    | zero => intro w hw; exact Or.inr (hw ▸ Relation.ReflTransGen.refl)
    | succ m ih =>
      rintro w (hw | ⟨z, hz, hzw⟩)
      · exact ih w hw
      · rcases ih z hz with hacc | hrz
        · exact Or.inl hacc
        · by_cases hwN : w = N
          · subst hwN
            refine Or.inl ⟨z, hrz, ?_⟩
            have := hzw.2
            rwa [if_pos rfl] at this
          · exact Or.inr (hrz.tail (hE'E _ _ hwN hzw))
  constructor
  · rintro ⟨v, hv, hacc⟩
    obtain ⟨m, hm⟩ := reflTransGen_iff_steps.1 hv
    have hvlt : v < N := by
      refine Steps_prop_of_edge (P := fun w => w < N) ?_ (M.init_lt n) hm
      intro a b hab
      exact (M.step_lt n _ _ _ hab).2
    have hm' : Steps E' m (M.init n) v := Steps_mono_rel hEE' hm
    have hlast : E' v N := ⟨hvlt, by rw [if_pos rfl]; exact hacc⟩
    have : Steps E' (m + 1) (M.init n) N := Or.inr ⟨v, hm', hlast⟩
    have hsat : Steps E' (N + 1) (M.init n) N :=
      Steps_saturate hE'le (M.init_lt n).le this
    exact Steps_mono hK hsat
  · intro h
    rcases hpath _ N h with hacc | hrz
    · exact hacc
    · exact absurd (hRTGlt N hrz) (by omega)

theorem savitch_init_valid (M : NMachine) (s : ℕ → ℕ) (n : ℕ) :
    SValid (M.size n) (s n + 1)
      ((none, [⟨M.init n, M.size n, s n + 1, 0, false⟩]) : SState) := by
  refine ⟨by simp, ?_⟩
  intro F hF
  simp only [List.mem_singleton] at hF
  subst hF
  exact ⟨le_rfl, (M.init_lt n).le, le_rfl, Nat.zero_le _⟩

/-- The deterministic machine simulating `M` by the recursive midpoint search. -/
noncomputable def savitchMachine (M : NMachine) (s : ℕ → ℕ) : DMachine where
  Conf := fun n => {p : SState // SValid (M.size n) (s n + 1) p}
  init := fun n => ⟨(none, [⟨M.init n, M.size n, s n + 1, 0, false⟩]), savitch_init_valid M s n⟩
  ipos := fun n p => spos (M.ipos n) p.1
  step := fun n b p => ⟨sstep (M.size n) (M.edgeAll n) b p.1, sstep_valid _ b p.2⟩
  acc := fun _ p => p.1 = (some true, [])

theorem savitchMachine_accepts (M : NMachine) (s : ℕ → ℕ) (x : List Bool)
    (hs : M.size x.length ≤ 2 ^ s x.length) :
    (savitchMachine M s).Accepts x ↔ M.Accepts x := by
  have hiter : ∀ t : ℕ,
      (((savitchMachine M s).next x)^[t] ((savitchMachine M s).init x.length)).1
        = (srun (M.size x.length) (M.edgeAll x.length) (M.ipos x.length) (bitAt x))^[t]
            (none, [⟨M.init x.length, M.size x.length, s x.length + 1, 0, false⟩]) := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  have hK : M.size x.length + 1 ≤ 2 ^ (s x.length + 1) := by
    have h1 : (1 : ℕ) ≤ 2 ^ s x.length := Nat.one_le_two_pow
    have h2 : 2 ^ (s x.length + 1) = 2 ^ (s x.length) + 2 ^ (s x.length) := by
      rw [pow_succ]; ring
    omega
  have hE := M.edgeAll_le x.length (M.ipos x.length) (bitAt x)
  rw [M.accepts_iff_steps x hK,
    ← sim_accepts hE (M.init x.length) (M.size x.length) (s x.length + 1)
      (M.init_lt x.length).le le_rfl]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← hiter t]
    exact ht
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    show (((savitchMachine M s).next x)^[t] ((savitchMachine M s).init x.length)).1
      = (some true, [])
    rw [hiter t]
    exact ht

/-- **Savitch's theorem**: nondeterministic space `f` is contained in deterministic space
`f ^ 2`. -/
theorem savitch (f : ℕ → ℕ) : NSPACE f ⊆ DSPACE (fun n => (f n) ^ 2) := by
  rintro L ⟨M, c, hsb, hL⟩
  refine ⟨savitchMachine M (fun n => c * (f n + 1)), 18 * (c + 2) ^ 2, ?_, ?_⟩
  · intro n
    obtain ⟨e⟩ := svalid_small (N := M.size n) (K := c * (f n + 1) + 1) (s := c * (f n + 1))
      (hsb n) rfl
    have hle : 2 ^ (6 * (c * (f n + 1) + 2) ^ 2) ≤ 2 ^ (18 * (c + 2) ^ 2 * ((f n) ^ 2 + 1)) := by
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith [sq_nonneg (f n), sq_nonneg c, sq_nonneg (c * f n), Nat.zero_le (c * f n)]
    exact ⟨e.trans (Fin.castLEEmb hle)⟩
  · intro x
    rw [hL x, ← savitchMachine_accepts M (fun n => c * (f n + 1)) x (hsb x.length)]

/-- Polynomial space. -/
def PSPACE : Set Language := {L | ∃ k, L ∈ DSPACE (fun n => n ^ k)}

/-- Nondeterministic polynomial space. -/
def NPSPACE : Set Language := {L | ∃ k, L ∈ NSPACE (fun n => n ^ k)}

open Classical in
/-- A deterministic machine, viewed as a nondeterministic one on the configuration space
`Fin (sz n)`. -/
noncomputable def dToN (D : DMachine) (sz : ℕ → ℕ) (e : (n : ℕ) → D.Conf n ↪ Fin (sz n)) :
    NMachine where
  size := sz
  init := fun n => ((e n (D.init n)) : ℕ)
  ipos := fun n i => if h : ∃ w : D.Conf n, ((e n w) : ℕ) = i then D.ipos n h.choose else 0
  step := fun n b i j => ∃ w : D.Conf n, ((e n w) : ℕ) = i ∧ ((e n (D.step n b w)) : ℕ) = j
  acc := fun n i => ∃ w : D.Conf n, ((e n w) : ℕ) = i ∧ D.acc n w
  init_lt := fun n => (e n (D.init n)).isLt
  step_lt := by
    rintro n b i j ⟨w, rfl, rfl⟩
    exact ⟨(e n w).isLt, (e n (D.step n b w)).isLt⟩

theorem dToN_accepts (D : DMachine) (sz : ℕ → ℕ) (e : (n : ℕ) → D.Conf n ↪ Fin (sz n))
    (x : List Bool) : (dToN D sz e).Accepts x ↔ D.Accepts x := by
  classical
  set n := x.length
  have hval_inj : ∀ (w w' : D.Conf n), ((e n w) : ℕ) = ((e n w') : ℕ) → w = w' := by
    intro w w' h
    exact (e n).injective (Fin.ext h)
  have hipos : ∀ w : D.Conf n, (dToN D sz e).ipos n ((e n w) : ℕ) = D.ipos n w := by
    intro w
    have hex : ∃ w' : D.Conf n, ((e n w') : ℕ) = ((e n w) : ℕ) := ⟨w, rfl⟩
    show (if h : ∃ w' : D.Conf n, ((e n w') : ℕ) = ((e n w) : ℕ) then D.ipos n h.choose else 0)
      = D.ipos n w
    rw [dif_pos hex]
    congr 1
    exact hval_inj _ _ hex.choose_spec
  have hedge : ∀ (w : D.Conf n) (j : ℕ),
      (dToN D sz e).edge x ((e n w) : ℕ) j ↔ j = ((e n (D.next x w)) : ℕ) := by
    intro w j
    rw [NMachine.edge, hipos w]
    constructor
    · rintro ⟨w', hw', rfl⟩
      rw [hval_inj w' w hw']
      rfl
    · rintro rfl
      exact ⟨w, rfl, rfl⟩
  have hreach : ∀ v : ℕ, Relation.ReflTransGen ((dToN D sz e).edge x) ((e n (D.init n)) : ℕ) v ↔
      ∃ t : ℕ, v = ((e n (((D.next x)^[t]) (D.init n))) : ℕ) := by
    intro v
    constructor
    · intro h
      induction h with
      | refl => exact ⟨0, rfl⟩
      | tail hab hbc ih =>
        obtain ⟨t, rfl⟩ := ih
        refine ⟨t + 1, ?_⟩
        rw [Function.iterate_succ_apply']
        exact (hedge _ _).1 hbc
    · rintro ⟨t, rfl⟩
      induction t with
      | zero => exact Relation.ReflTransGen.refl
      | succ t ih =>
        refine ih.tail ?_
        rw [Function.iterate_succ_apply']
        exact (hedge _ _).2 rfl
  constructor
  · rintro ⟨v, hv, w, hw, hacc⟩
    obtain ⟨t, rfl⟩ := (hreach v).1 hv
    exact ⟨t, by rwa [hval_inj w _ hw] at hacc⟩
  · rintro ⟨t, ht⟩
    exact ⟨((e n (((D.next x)^[t]) (D.init n))) : ℕ), (hreach _).2 ⟨t, rfl⟩, ⟨_, rfl, ht⟩⟩

/-- Deterministic machines are a special case of nondeterministic ones. -/
theorem dspace_subset_nspace (f : ℕ → ℕ) : DSPACE f ⊆ NSPACE f := by
  classical
  rintro L ⟨D, c, hsb, hL⟩
  refine ⟨dToN D (fun n => 2 ^ (c * (f n + 1))) (fun n => (hsb n).some), c, fun n => le_rfl, ?_⟩
  intro x
  rw [hL x, dToN_accepts]

/-! ## A sanity check: the classes are not trivial

A machine only sees the bit of the input at the position determined by its current
configuration, so membership in these classes is a genuine computational statement.  Here is a
simple language that is decided in space `0`. -/

/-- A machine that reads the first bit of its input and remembers it. -/
def firstBitMachine : DMachine where
  Conf := fun _ => Option Bool
  init := fun _ => none
  ipos := fun _ _ => 0
  step := fun _ b c => match c with
    | none => some b
    | some d => some d
  acc := fun _ c => c = some true

/-- The language of strings whose first bit is `true` is decided in space `0`. -/
theorem firstBit_mem_dspace : (fun x => bitAt x 0 = true) ∈ DSPACE (fun _ => 0) := by
  refine ⟨firstBitMachine, 2, fun n => ?_, fun x => ?_⟩
  · refine ⟨(Fintype.equivFin (Option Bool)).toEmbedding.trans (Fin.castLEEmb ?_)⟩
    simp
  · have h1 : ∀ t : ℕ, (firstBitMachine.next x)^[t + 1] (firstBitMachine.init x.length)
        = some (bitAt x 0) := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih => rw [Function.iterate_succ_apply', ih]; rfl
    constructor
    · intro hx
      exact ⟨1, by rw [h1 0, hx]; rfl⟩
    · rintro ⟨t, ht⟩
      cases t with
      | zero => exact absurd ht (by simp [firstBitMachine])
      | succ t =>
        rw [h1 t] at ht
        simpa [firstBitMachine] using ht

/-- `PSPACE = NPSPACE`. -/
theorem pspace_eq_npspace : PSPACE = NPSPACE := by
  apply Set.eq_of_subset_of_subset
  · rintro L ⟨k, hk⟩
    exact ⟨k, dspace_subset_nspace _ hk⟩
  · rintro L ⟨k, hk⟩
    refine ⟨2 * k, ?_⟩
    have h := savitch (fun n => n ^ k) hk
    have heq : (fun n : ℕ => (n ^ k) ^ 2) = (fun n : ℕ => n ^ (2 * k)) := by
      funext n
      rw [← pow_mul, Nat.mul_comm]
    rwa [heq] at h

end CS

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

