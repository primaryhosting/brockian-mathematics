/-!
# P Vs NP Statement
Category: Frontier — Moonshot
Target: Frontier.P_vs_NP_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses only the Lean 4 core library),
so that the formal statement of the P vs NP problem depends on as little as possible.

We define:
* single-tape deterministic Turing machines and their step-by-step semantics;
* single-tape nondeterministic Turing machines and their reachability semantics;
* the classes `Frontier.P` and `Frontier.NP` of languages decidable in polynomial time by
  deterministic resp. nondeterministic machines;
* polynomial-time computable functions, polynomial-time many-one reducibility `≤p`,
  NP-hardness and NP-completeness;
* the proposition `Frontier.PNeqNP`, i.e. `P ≠ NP`.

The main theorem `Frontier.P_vs_NP_statement` records the precise statement together with
its standard reformulation: `P ≠ NP` holds if and only if some language is decidable in
nondeterministic polynomial time but not in deterministic polynomial time.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Frontier

/-! ## Words and languages -/

/-- Inputs are finite binary strings. -/
abbrev Word : Type := List Bool

/-- The tape alphabet: `none` is the blank symbol, `some b` a binary symbol. -/
abbrev Sym : Type := Option Bool

/-- A language is a set of binary strings, represented by its characteristic predicate. -/
abbrev Language : Type := Word → Prop

/-- Head movement directions. -/
inductive Dir : Type
  | left : Dir
  | right : Dir
  | stay : Dir
  deriving DecidableEq

/-- Moving the head position according to a direction. -/
def Dir.apply : Dir → Int → Int
  | Dir.left, p => p - 1
  | Dir.right, p => p + 1
  | Dir.stay, p => p

/-- The two-way infinite tape holding the input `w`: cell `i` contains the `i`-th bit of
`w` for `0 ≤ i < |w|`, and is blank everywhere else. -/
def initTape (w : Word) : Int → Sym := fun i => if 0 ≤ i then w[i.toNat]? else none

/-- Writing the symbol `s` at position `p` of a tape. -/
def writeTape (tape : Int → Sym) (p : Int) (s : Sym) : Int → Sym :=
  fun i => if i = p then s else tape i

/-- A configuration of a machine with `n` states: current state, tape contents and head
position. -/
structure Cfg (n : Nat) : Type where
  q : Fin n
  tape : Int → Sym
  pos : Int

/-! ## Deterministic Turing machines -/

/-- A deterministic single-tape Turing machine with state set `Fin size`, a distinguished
start state, accepting state and rejecting state, and a transition function which, given
the current state and scanned symbol, returns the next state, the symbol to write and the
head movement. -/
structure TM : Type where
  size : Nat
  init : Fin size
  acc : Fin size
  rej : Fin size
  δ : Fin size → Sym → Fin size × Sym × Dir

/-- A configuration is halting if its state is the accepting or the rejecting state. -/
def TM.Halted (M : TM) (c : Cfg M.size) : Prop := c.q = M.acc ∨ c.q = M.rej

instance (M : TM) (c : Cfg M.size) : Decidable (M.Halted c) := by
  unfold TM.Halted; infer_instance

/-- One computation step; halting configurations are fixed points. -/
def TM.step (M : TM) (c : Cfg M.size) : Cfg M.size :=
  if M.Halted c then c
  else
    let r := M.δ c.q (c.tape c.pos)
    ⟨r.1, writeTape c.tape c.pos r.2.1, r.2.2.apply c.pos⟩

/-- The starting configuration of `M` on input `w`. -/
def TM.initCfg (M : TM) (w : Word) : Cfg M.size := ⟨M.init, initTape w, 0⟩

/-- Iterating the step function. -/
def TM.iter (M : TM) : Nat → Cfg M.size → Cfg M.size
  | 0, c => c
  | (t + 1), c => M.iter t (M.step c)

/-- The configuration reached by `M` after `t` steps on input `w`. -/
def TM.run (M : TM) (w : Word) : Nat → Cfg M.size
  | 0 => M.initCfg w
  | (t + 1) => M.step (M.run w t)

/-! ## Time bounds -/

/-- `f` is bounded by a polynomial. -/
def Poly (f : Nat → Nat) : Prop := ∃ c k : Nat, ∀ n : Nat, f n ≤ c * (n + 1) ^ k

/-- `M` decides the language `L` within time `f`: on every input `w`, within `f |w|`
steps the machine halts, and it halts in the accepting state exactly when `w ∈ L`. -/
def TM.DecidesInTime (M : TM) (L : Language) (f : Nat → Nat) : Prop :=
  ∀ w : Word, ∃ t, t ≤ f w.length ∧
    M.Halted (M.run w t) ∧ ((M.run w t).q = M.acc ↔ L w)

/-- The complexity class `P`: the languages decided by some deterministic Turing machine
within a polynomial time bound. -/
def P : Language → Prop := fun L => ∃ (M : TM) (f : Nat → Nat), Poly f ∧ M.DecidesInTime L f

/-! ## Nondeterministic Turing machines -/

/-- A nondeterministic single-tape Turing machine: the transition relation may allow
several successor triples for a given state and scanned symbol. -/
structure NTM : Type where
  size : Nat
  init : Fin size
  acc : Fin size
  δ : Fin size → Sym → Fin size → Sym → Dir → Prop

/-- The one-step relation of a nondeterministic machine. -/
def NTM.Step (N : NTM) (c c' : Cfg N.size) : Prop :=
  ∃ (q' : Fin N.size) (s : Sym) (d : Dir), N.δ c.q (c.tape c.pos) q' s d ∧
    c' = ⟨q', writeTape c.tape c.pos s, d.apply c.pos⟩

/-- `N.ReachIn t c c'` says that `c'` is reachable from `c` in exactly `t` steps. -/
def NTM.ReachIn (N : NTM) : Nat → Cfg N.size → Cfg N.size → Prop
  | 0, c, c' => c = c'
  | (t + 1), c, c'' => ∃ c', N.Step c c' ∧ N.ReachIn t c' c''

/-- `N` accepts `w` within `t` steps: some computation path of length at most `t` starting
from the initial configuration on `w` reaches the accepting state. -/
def NTM.AcceptsIn (N : NTM) (w : Word) (t : Nat) : Prop :=
  ∃ s, s ≤ t ∧ ∃ c : Cfg N.size,
    N.ReachIn s ⟨N.init, initTape w, 0⟩ c ∧ c.q = N.acc

/-- `N` decides `L` within time `f`: `w ∈ L` if and only if `N` has an accepting
computation on `w` of length at most `f |w|`. -/
def NTM.DecidesInTime (N : NTM) (L : Language) (f : Nat → Nat) : Prop :=
  ∀ w : Word, (L w ↔ N.AcceptsIn w (f w.length))

/-- The complexity class `NP`: the languages decided by some nondeterministic Turing
machine within a polynomial time bound. -/
def NP : Language → Prop :=
  fun L => ∃ (N : NTM) (f : Nat → Nat), Poly f ∧ N.DecidesInTime L f

/-! ## Polynomial-time computable functions and reducibility -/

/-- The configuration `c` has output `v`: the tape contains exactly `v` in the cells
`0, …, |v| - 1`, and the cell `|v|` is blank. -/
def CfgOutput {n : Nat} (c : Cfg n) (v : Word) : Prop :=
  (∀ i : Nat, i < v.length → c.tape (i : Int) = v[i]?) ∧ c.tape (v.length : Int) = none

/-- `M` computes the function `g` within time `f`. -/
def TM.ComputesInTime (M : TM) (g : Word → Word) (f : Nat → Nat) : Prop :=
  ∀ w : Word, ∃ t, t ≤ f w.length ∧ M.Halted (M.run w t) ∧ CfgOutput (M.run w t) (g w)

/-- `g` is computable in polynomial time. -/
def PolyComputable (g : Word → Word) : Prop :=
  ∃ (M : TM) (f : Nat → Nat), Poly f ∧ M.ComputesInTime g f

/-- Polynomial-time many-one reducibility: `L ≤p L'` when some polynomial-time computable
function `g` satisfies `w ∈ L ↔ g w ∈ L'`. -/
def PolyReducible (L L' : Language) : Prop :=
  ∃ g : Word → Word, PolyComputable g ∧ ∀ w : Word, L w ↔ L' (g w)

@[inherit_doc] infix:50 " ≤p " => PolyReducible

/-- `L'` is `NP`-hard: every language in `NP` reduces to it in polynomial time. -/
def NPHard (L' : Language) : Prop := ∀ L : Language, NP L → L ≤p L'

/-- `L'` is `NP`-complete: it lies in `NP` and is `NP`-hard. -/
def NPComplete (L' : Language) : Prop := NP L' ∧ NPHard L'

/-! ## Basic facts about deterministic runs -/

theorem TM.step_of_halted (M : TM) {c : Cfg M.size} (h : M.Halted c) : M.step c = c := by
  simp [TM.step, h]

theorem TM.run_succ (M : TM) (w : Word) (t : Nat) : M.run w (t + 1) = M.step (M.run w t) :=
  rfl

theorem TM.iter_succ (M : TM) (t : Nat) (c : Cfg M.size) :
    M.iter (t + 1) c = M.step (M.iter t c) := by
  induction t generalizing c with
  | zero => rfl
  | succ n ih => exact ih (M.step c)

theorem TM.run_eq_iter (M : TM) (w : Word) (t : Nat) :
    M.run w t = M.iter t (M.initCfg w) := by
  induction t with
  | zero => rfl
  | succ n ih => rw [M.run_succ, ih, M.iter_succ]

theorem TM.run_eq_of_halted (M : TM) {w : Word} {t : Nat} (h : M.Halted (M.run w t))
    {t' : Nat} (ht : t ≤ t') : M.run w t' = M.run w t := by
  induction t' with
  | zero =>
    have : t = 0 := Nat.le_zero.mp ht
    rw [this]
  | succ n ih =>
    cases Nat.lt_or_ge n t with
    | inl hlt =>
      have : t = n + 1 := by omega
      rw [this]
    | inr hge =>
      rw [M.run_succ, ih hge, M.step_of_halted h]

/-! ## Simulating a deterministic machine by a nondeterministic one -/

/-- Every deterministic machine is in particular a nondeterministic machine. -/
def TM.toNTM (M : TM) : NTM where
  size := M.size
  init := M.init
  acc := M.acc
  δ := fun q s q' s' d => ¬ (q = M.acc ∨ q = M.rej) ∧ M.δ q s = (q', s', d)

theorem TM.toNTM_step_iff (M : TM) (c c' : Cfg M.size) :
    M.toNTM.Step c c' ↔ ¬ M.Halted c ∧ c' = M.step c := by
  constructor
  · intro h
    have ⟨q', s, d, ⟨hnh, heq⟩, hc'⟩ := h
    have hnh' : ¬ M.Halted c := hnh
    refine ⟨hnh', ?_⟩
    rw [hc']
    show (⟨q', writeTape c.tape c.pos s, d.apply c.pos⟩ : Cfg M.size) = M.step c
    unfold TM.step
    rw [if_neg hnh']
    simp only []
    rw [heq]
  · intro h
    have hnh : ¬ M.Halted c := h.1
    refine ⟨(M.δ c.q (c.tape c.pos)).1, (M.δ c.q (c.tape c.pos)).2.1,
      (M.δ c.q (c.tape c.pos)).2.2, ⟨hnh, rfl⟩, ?_⟩
    rw [h.2]
    unfold TM.step
    rw [if_neg hnh]

/-- Reachability in the simulating nondeterministic machine follows the deterministic
run. -/
theorem TM.toNTM_reach_eq (M : TM) {t : Nat} {c c' : Cfg M.size}
    (h : M.toNTM.ReachIn t c c') : c' = M.iter t c := by
  induction t generalizing c with
  | zero => exact h.symm
  | succ n ih =>
    have ⟨d, hd, hrest⟩ := h
    have hd' := (M.toNTM_step_iff c d).mp hd
    have := ih (hd'.2 ▸ hrest)
    rw [this]
    rfl

theorem NTM.reachIn_snoc (N : NTM) {t : Nat} {c c' c'' : Cfg N.size}
    (h : N.ReachIn t c c') (hs : N.Step c' c'') : N.ReachIn (t + 1) c c'' := by
  induction t generalizing c with
  | zero =>
    show ∃ d, N.Step c d ∧ N.ReachIn 0 d c''
    exact ⟨c'', h ▸ hs, rfl⟩
  | succ n ih =>
    have ⟨d, hd, hrest⟩ := h
    exact ⟨d, hd, ih hrest⟩

/-- Every configuration of the deterministic run is reachable in the simulating
nondeterministic machine, in at most that many steps (in fewer steps if the machine has
already halted). -/
theorem TM.toNTM_reach_run (M : TM) (w : Word) (t : Nat) :
    ∃ s, s ≤ t ∧ M.toNTM.ReachIn s ⟨M.toNTM.init, initTape w, 0⟩ (M.run w t) ∧
      M.run w s = M.run w t := by
  induction t with
  | zero => exact ⟨0, Nat.le_refl 0, rfl, rfl⟩
  | succ n ih =>
    have ⟨s, hs, hreach, hrun⟩ := ih
    by_cases h : M.Halted (M.run w n)
    · refine ⟨s, by omega, ?_, ?_⟩
      · rw [M.run_succ, M.step_of_halted h]; exact hreach
      · rw [M.run_succ, M.step_of_halted h]; exact hrun
    · refine ⟨s + 1, by omega, ?_, ?_⟩
      · refine M.toNTM.reachIn_snoc hreach ?_
        exact (M.toNTM_step_iff _ _).mpr ⟨h, rfl⟩
      · show M.step (M.run w s) = M.run w (n + 1)
        rw [hrun]
        exact (M.run_succ w n).symm

/-- The simulating nondeterministic machine decides the same language within the same
time bound. -/
theorem TM.toNTM_decidesInTime (M : TM) {L : Language} {f : Nat → Nat}
    (h : M.DecidesInTime L f) : M.toNTM.DecidesInTime L f := by
  intro w
  have ⟨t, ht, hhalt, hiff⟩ := h w
  constructor
  · intro hw
    have ⟨s, hs, hreach, _hrun⟩ := M.toNTM_reach_run w t
    exact ⟨s, Nat.le_trans hs ht, _, hreach, hiff.mpr hw⟩
  · intro hacc
    have ⟨s, hs, c, hreach, hc⟩ := hacc
    have hcs : c = M.run w s := by
      rw [M.toNTM_reach_eq hreach, M.run_eq_iter]
      rfl
    have hc' : (M.run w s).q = M.acc := hcs ▸ hc
    have hhalt' : M.Halted (M.run w s) := Or.inl hc'
    cases Nat.le_total s t with
    | inl hst =>
      have heq : M.run w t = M.run w s := M.run_eq_of_halted hhalt' hst
      exact hiff.mp (by rw [heq]; exact hc')
    | inr hts =>
      have heq : M.run w s = M.run w t := M.run_eq_of_halted hhalt hts
      exact hiff.mp (by rw [← heq]; exact hc')

/-! ## `P ⊆ NP` -/

/-- Every language decidable in deterministic polynomial time is decidable in
nondeterministic polynomial time. -/
theorem P_subset_NP : ∀ L : Language, P L → NP L := by
  intro L hL
  have ⟨M, f, hf, hdec⟩ := hL
  exact ⟨M.toNTM, f, hf, M.toNTM_decidesInTime hdec⟩

/-! ## Reflexivity of polynomial-time reducibility -/

/-- The machine that immediately halts in its (unique) accepting state, leaving the tape
untouched; it computes the identity function in time `0`. -/
def idTM : TM where
  size := 1
  init := ⟨0, by omega⟩
  acc := ⟨0, by omega⟩
  rej := ⟨0, by omega⟩
  δ := fun q s => (q, s, Dir.stay)

theorem polyComputable_id : PolyComputable (fun w : Word => w) := by
  refine ⟨idTM, fun _ => 0, ⟨0, 0, fun n => Nat.zero_le _⟩, ?_⟩
  intro w
  refine ⟨0, Nat.le_refl 0, Or.inl rfl, ?_, ?_⟩
  · intro i hi
    show initTape w (i : Int) = _
    unfold initTape
    rw [if_pos (by omega : (0 : Int) ≤ (i : Int))]
    have : ((i : Int)).toNat = i := by omega
    rw [this]
  · show initTape w (w.length : Int) = none
    unfold initTape
    rw [if_pos (by omega : (0 : Int) ≤ (w.length : Int))]
    have : ((w.length : Int)).toNat = w.length := by omega
    rw [this]
    exact List.getElem?_eq_none (Nat.le_refl _)

/-- The machine that immediately halts in its rejecting state (which is distinct from its
accepting state). -/
def rejTM : TM where
  size := 2
  init := ⟨1, by omega⟩
  acc := ⟨0, by omega⟩
  rej := ⟨1, by omega⟩
  δ := fun q s => (q, s, Dir.stay)

/-- Sanity check: the language of all words is in `P`. -/
theorem univ_mem_P : P (fun _ => True) := by
  refine ⟨idTM, fun _ => 0, ⟨0, 0, fun _ => Nat.zero_le _⟩, ?_⟩
  intro w
  exact ⟨0, Nat.le_refl 0, Or.inl rfl, fun _ => trivial, fun _ => rfl⟩

/-- Sanity check: the empty language is in `P`. -/
theorem empty_mem_P : P (fun _ => False) := by
  refine ⟨rejTM, fun _ => 0, ⟨0, 0, fun _ => Nat.zero_le _⟩, ?_⟩
  intro w
  refine ⟨0, Nat.le_refl 0, Or.inr rfl, ?_, ?_⟩
  · intro hacc
    have h10 : (1 : Nat) = 0 := congrArg Fin.val hacc
    omega
  · intro hfalse
    exact hfalse.elim

/-- Polynomial-time many-one reducibility is reflexive. -/
theorem polyReducible_refl (L : Language) : L ≤p L :=
  ⟨fun w => w, polyComputable_id, fun _ => Iff.rfl⟩

/-! ## The statement of the P vs NP problem -/

/-- The P vs NP problem: the class of languages decidable in deterministic polynomial time
differs from the class of languages decidable in nondeterministic polynomial time. -/
def PNeqNP : Prop := P ≠ NP

/-- **Statement of the P vs NP problem.**  With `P` and `NP` defined via time-bounded
deterministic resp. nondeterministic Turing machines, the assertion `P ≠ NP` is equivalent
to the existence of a language that is decidable in nondeterministic polynomial time but
not in deterministic polynomial time.

(The truth value of `P ≠ NP` is of course unknown; this theorem records the precise formal
statement together with its standard reformulation, which rests on the inclusion
`P ⊆ NP`.) -/
theorem P_vs_NP_statement : PNeqNP ↔ ∃ L : Language, NP L ∧ ¬ P L := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hcon
    have hsub : ∀ L : Language, NP L → P L := by
      intro L hL
      apply Classical.byContradiction
      intro hnp
      exact hcon ⟨L, hL, hnp⟩
    exact h (funext fun L => propext ⟨fun hp => P_subset_NP L hp, fun hn => hsub L hn⟩)
  · intro hex hEq
    have ⟨L, hNP, hP⟩ := hex
    exact hP (hEq ▸ hNP)

end Frontier

