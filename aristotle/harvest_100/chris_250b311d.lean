/-
The configuration graph of a space bounded nondeterministic machine, and the
deterministic middle-first search run on it.
-/
import RequestProject.NTM

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace CS
namespace Sim

variable (M : NTM) (s : ℕ) (x : List Bool)

/-- Vertices of the configuration graph: the configurations of `M`, plus a sink
`none` which is entered from every accepting configuration. -/
abbrev Node : Type := Option (Conf M x.length s)

/-- Edges of the configuration graph.  A single edge query only inspects the
local transition table of `M` at the scanned symbols. -/
def edge : Node M s x → Node M s x → Bool
  | some c, some c' => stepB M x c c'
  | some c, none => decide (c.1 = M.acc)
  | none, some _ => false
  | none, none => true

/-- The list of all vertices. -/
def nodes : List (Node M s x) := (Finset.univ : Finset (Node M s x)).toList

theorem mem_nodes (v : Node M s x) : v ∈ nodes M s x :=
  Finset.mem_toList.2 (Finset.mem_univ v)

/-- The number of vertices of the configuration graph. -/
def numNodes : ℕ := Fintype.card (Node M s x)

/-- The recursion depth used by Savitch's algorithm: `⌈log₂ (number of
configurations)⌉`. -/
def depth : ℕ := Nat.clog 2 (numNodes M s x)

/-- The initial vertex. -/
def source : Node M s x := some (initConf M x.length s)

/-- One step of the deterministic search machine on the configuration graph. -/
def detStep : Savitch.Cfg (Node M s x) → Savitch.Cfg (Node M s x) :=
  Savitch.step (edge M s x) (nodes M s x)

/-- The initial configuration of the deterministic search machine: it asks
whether the sink is reachable from the initial configuration of `M` within
`2 ^ depth` steps. -/
def detInit : Savitch.Cfg (Node M s x) :=
  Savitch.Cfg.call (depth M s x) (source M s x) none []

/-! ### Acceptance is reachability of the sink -/

theorem reach_of_accepts (h : M.AcceptsIn s x) :
    Relation.ReflTransGen (fun a b => edge M s x a b = true) (source M s x) none := by
  obtain ⟨c, hc, hacc⟩ := h
  have h1 : Relation.ReflTransGen (fun a b => edge M s x a b = true)
      (some (initConf M x.length s)) (some c) := by
    refine Relation.ReflTransGen.lift (fun c => (some c : Node M s x)) ?_ hc
    intro a b hab
    simpa [edge] using hab
  refine h1.tail ?_
  simpa [edge] using hacc

theorem reach_key (b : Node M s x)
    (hb : Relation.ReflTransGen (fun a b => edge M s x a b = true) (source M s x) b) :
    (∀ c, b = some c →
        Relation.ReflTransGen (fun a b => stepB M x a b = true) (initConf M x.length s) c) ∧
      (b = none → M.AcceptsIn s x) := by
  induction hb with
  | refl =>
      constructor
      · intro c hc
        have : c = initConf M x.length s := by
          simpa [source] using hc.symm
        subst this
        exact Relation.ReflTransGen.refl
      · intro h
        simp [source] at h
  | tail hab hbc ih =>
      rename_i b1 b2 _
      constructor
      · intro c hc
        subst hc
        rcases b1 with _ | c1
        · simp [edge] at hbc
        · have hstep : stepB M x c1 c = true := by simpa [edge] using hbc
          exact (ih.1 c1 rfl).tail hstep
      · intro hc
        subst hc
        rcases b1 with _ | c1
        · exact ih.2 rfl
        · have hacc : c1.1 = M.acc := by simpa [edge] using hbc
          exact ⟨c1, ih.1 c1 rfl, hacc⟩

theorem accepts_of_reach
    (h : Relation.ReflTransGen (fun a b => edge M s x a b = true) (source M s x) none) :
    M.AcceptsIn s x :=
  (reach_key M s x none h).2 rfl

theorem accepts_iff_reach :
    M.AcceptsIn s x ↔
      Relation.ReflTransGen (fun a b => edge M s x a b = true) (source M s x) none :=
  ⟨reach_of_accepts M s x, accepts_of_reach M s x⟩

/-! ### Acceptance is decided by the bounded search -/

theorem numNodes_le_pow : numNodes M s x ≤ 2 ^ depth M s x :=
  Nat.le_pow_clog (by norm_num) _

theorem accepts_iff_sreach :
    M.AcceptsIn s x ↔ sreach (edge M s x) (nodes M s x) (depth M s x) (source M s x) none = true := by
  rw [sreach_iff (edge M s x) (nodes M s x) (mem_nodes M s x)]
  constructor
  · intro h
    have h1 := (accepts_iff_reach M s x).1 h
    have h2 := reachLe_card_of_reflTransGen h1
    exact reachLe_mono (le_trans (le_of_eq rfl) (numNodes_le_pow M s x)) h2
  · intro h
    exact (accepts_iff_reach M s x).2 (reachLe_reflTransGen h)

/-- **Correctness of the deterministic simulation.**  The deterministic machine
halts, and its answer is `true` exactly when `M` accepts. -/
theorem detRun_correct :
    ∃ (b : Bool) (n : ℕ), (detStep M s x)^[n] (detInit M s x) = Savitch.Cfg.done b ∧
      (b = true ↔ M.AcceptsIn s x) := by
  obtain ⟨n, hn⟩ :=
    Savitch.run_call (edge M s x) (nodes M s x) (depth M s x) (source M s x) none
  exact ⟨_, n, hn, (accepts_iff_sreach M s x).symm⟩

/-! ### The space bound -/

/-- **Space bound.**  At every moment the deterministic machine keeps at most
`depth` frames on its stack. -/
theorem detRun_stack_le (n : ℕ) :
    ((detStep M s x)^[n] (detInit M s x)).stack.length ≤ depth M s x :=
  Savitch.stack_length_le _ _ _ _ _ n

/-- **Space bound in bits**, for the cost model `Savitch.frameWidth`. -/
theorem detRun_bits_le (n : ℕ) :
    ((detStep M s x)^[n] (detInit M s x)).bits (depth M s x) (numNodes M s x)
      ≤ depth M s x * Savitch.frameWidth (depth M s x) (numNodes M s x) :=
  Savitch.bits_le _ _ _ _ _ _ n

/-! ### The depth is linear in the space bound -/

theorem clog_mul_le (a b : ℕ) : Nat.clog 2 (a * b) ≤ Nat.clog 2 a + Nat.clog 2 b := by
  refine Nat.clog_le_of_le_pow ?_
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) a) (Nat.le_pow_clog (by norm_num) b)

theorem clog_le_self (a : ℕ) : Nat.clog 2 a ≤ a :=
  Nat.clog_le_of_le_pow (le_of_lt (Nat.lt_two_pow_self))

/-- The number of vertices is at most `2 ^ D` for the "obvious" `D`. -/
theorem depth_le_aux :
    depth M s x ≤ Nat.clog 2 (Fintype.card M.Q) + Nat.clog 2 (x.length + 1)
      + (s + 1) * Nat.clog 2 (Fintype.card M.Γ) + Nat.clog 2 (s + 1) + 1 := by
  set cQ := Nat.clog 2 (Fintype.card M.Q) with hcQ
  set cn := Nat.clog 2 (x.length + 1) with hcn
  set cG := Nat.clog 2 (Fintype.card M.Γ) with hcG
  set cs := Nat.clog 2 (s + 1) with hcs
  have hQ : Fintype.card M.Q ≤ 2 ^ cQ := Nat.le_pow_clog (by norm_num) _
  have hn : x.length + 1 ≤ 2 ^ cn := Nat.le_pow_clog (by norm_num) _
  have hG : Fintype.card M.Γ ≤ 2 ^ cG := Nat.le_pow_clog (by norm_num) _
  have hs : s + 1 ≤ 2 ^ cs := Nat.le_pow_clog (by norm_num) _
  have hGpow : (Fintype.card M.Γ) ^ (s + 1) ≤ 2 ^ ((s + 1) * cG) := by
    calc (Fintype.card M.Γ) ^ (s + 1) ≤ (2 ^ cG) ^ (s + 1) := Nat.pow_le_pow_left hG _
      _ = 2 ^ (cG * (s + 1)) := by rw [← pow_mul]
      _ = 2 ^ ((s + 1) * cG) := by rw [Nat.mul_comm]
  have hcard : Fintype.card (Conf M x.length s) ≤ 2 ^ (cQ + cn + (s + 1) * cG + cs) := by
    rw [card_conf]
    calc Fintype.card M.Q * ((x.length + 1) * (Fintype.card M.Γ ^ (s + 1) * (s + 1)))
        ≤ 2 ^ cQ * (2 ^ cn * (2 ^ ((s + 1) * cG) * 2 ^ cs)) := by
          exact Nat.mul_le_mul hQ (Nat.mul_le_mul hn (Nat.mul_le_mul hGpow hs))
      _ = 2 ^ (cQ + cn + (s + 1) * cG + cs) := by ring
  have hnum : numNodes M s x ≤ 2 ^ (cQ + cn + (s + 1) * cG + cs + 1) := by
    have hcardN : numNodes M s x = Fintype.card (Conf M x.length s) + 1 := by
      simp [numNodes, Node]
    have hpos : (1 : ℕ) ≤ 2 ^ (cQ + cn + (s + 1) * cG + cs) := Nat.one_le_two_pow
    rw [hcardN, pow_succ]
    omega
  exact Nat.clog_le_of_le_pow hnum

/-- The recursion depth is linear in `s + log |x|`, with a constant depending
only on the machine. -/
theorem depth_le :
    depth M s x
      ≤ (Nat.clog 2 (Fintype.card M.Q) + Nat.clog 2 (Fintype.card M.Γ) + 3)
        * (s + Nat.clog 2 (x.length + 1) + 1) := by
  set cQ := Nat.clog 2 (Fintype.card M.Q) with hcQ
  set cn := Nat.clog 2 (x.length + 1) with hcn
  set cG := Nat.clog 2 (Fintype.card M.Γ) with hcG
  set T := s + cn + 1 with hT
  have hT1 : 1 ≤ T := by omega
  have h1 : cQ ≤ cQ * T := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : cn ≤ T := by omega
  have h3 : (s + 1) * cG ≤ T * cG := Nat.mul_le_mul_right _ (by omega)
  have h4 : Nat.clog 2 (s + 1) ≤ T := le_trans (clog_le_self _) (by omega)
  have h5 : depth M s x ≤ cQ + cn + (s + 1) * cG + Nat.clog 2 (s + 1) + 1 := depth_le_aux M s x
  calc depth M s x ≤ cQ + cn + (s + 1) * cG + Nat.clog 2 (s + 1) + 1 := h5
    _ ≤ cQ * T + T + T * cG + T + T := by omega
    _ = (cQ + cG + 3) * T := by ring

/-- The width of a frame is at most `5 · depth + 1` bits. -/
theorem frameWidth_le :
    Savitch.frameWidth (depth M s x) (numNodes M s x) ≤ 5 * depth M s x + 1 := by
  have h : Nat.clog 2 (depth M s x) ≤ depth M s x := clog_le_self _
  have h2 : Nat.clog 2 (numNodes M s x) = depth M s x := rfl
  simp only [Savitch.frameWidth, h2]
  omega

end Sim
end CS

/-
The deterministic middle-first search machine used in Savitch's theorem.

This is an explicit *small-step* deterministic machine.  Its memory is a stack
of frames; a single step inspects only the top frame (plus one bit of returned
information) and performs a single push, pop, or top-frame update, together
with at most one query of the edge relation `E`.  The two facts proved here are

* `CS.Savitch.run_call`        : the machine computes `sreach`, i.e. bounded reachability;
* `CS.Savitch.stack_length_le` : the stack never holds more than `K` frames,

which together give the `O(K · framewidth)` space bound of Savitch's algorithm.
-/
import RequestProject.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace CS
namespace Savitch

universe u

/-- A stack frame.  `mid1 k u v i m` means: we are computing
`sreach (k+1) u v`, are currently trying the `i`-th candidate midpoint `m`,
and are waiting for the result of the recursive call `sreach k u m`.
`mid2` is the same but waiting for the second call `sreach k m v`. -/
inductive Frame (V : Type u) where
  | mid1 (k : ℕ) (u v : V) (i : ℕ) (m : V)
  | mid2 (k : ℕ) (u v : V) (i : ℕ) (m : V)
  deriving DecidableEq

/-- The recursion level a frame is waiting on. -/
def Frame.level {V : Type u} : Frame V → ℕ
  | .mid1 k _ _ _ _ => k
  | .mid2 k _ _ _ _ => k

@[simp] theorem Frame.level_mid1 {V : Type u} (k : ℕ) (u v : V) (i : ℕ) (m : V) :
    (Frame.mid1 k u v i m).level = k := rfl

@[simp] theorem Frame.level_mid2 {V : Type u} (k : ℕ) (u v : V) (i : ℕ) (m : V) :
    (Frame.mid2 k u v i m).level = k := rfl

/-- The index of the candidate midpoint a frame is currently trying. -/
def Frame.idx {V : Type u} : Frame V → ℕ
  | .mid1 _ _ _ i _ => i
  | .mid2 _ _ _ i _ => i

@[simp] theorem Frame.idx_mid1 {V : Type u} (k : ℕ) (u v : V) (i : ℕ) (m : V) :
    (Frame.mid1 k u v i m).idx = i := rfl

@[simp] theorem Frame.idx_mid2 {V : Type u} (k : ℕ) (u v : V) (i : ℕ) (m : V) :
    (Frame.mid2 k u v i m).idx = i := rfl

/-- A configuration of the deterministic search machine. -/
inductive Cfg (V : Type u) where
  | call (k : ℕ) (u v : V) (st : List (Frame V))
  | ret (b : Bool) (st : List (Frame V))
  | done (b : Bool)

/-- The stack held in a configuration. -/
def Cfg.stack {V : Type u} : Cfg V → List (Frame V)
  | .call _ _ _ st => st
  | .ret _ st => st
  | .done _ => []

@[simp] theorem Cfg.stack_call {V : Type u} (k : ℕ) (u v : V) (st : List (Frame V)) :
    (Cfg.call k u v st).stack = st := rfl

@[simp] theorem Cfg.stack_ret {V : Type u} (b : Bool) (st : List (Frame V)) :
    (Cfg.ret b st).stack = st := rfl

@[simp] theorem Cfg.stack_done {V : Type u} (b : Bool) :
    (Cfg.done b : Cfg V).stack = [] := rfl

variable {V : Type u} [DecidableEq V]

/-- Start (or resume) the loop over candidate midpoints at index `i`. -/
def tryFrom (all : List V) (k : ℕ) (u v : V) (i : ℕ) (st : List (Frame V)) : Cfg V :=
  match all[i]? with
  | some m => .call k u m (.mid1 k u v i m :: st)
  | none => .ret false st

/-- One step of the deterministic search machine. -/
def step (E : V → V → Bool) (all : List V) : Cfg V → Cfg V
  | .call 0 u v st => .ret (decide (u = v) || E u v) st
  | .call (k + 1) u v st => tryFrom all k u v 0 st
  | .ret b [] => .done b
  | .ret b (.mid1 k u v i m :: st) =>
      if b then .call k m v (.mid2 k u v i m :: st) else tryFrom all k u v (i + 1) st
  | .ret b (.mid2 k u v i m :: st) =>
      if b then .ret true st else tryFrom all k u v (i + 1) st
  | .done b => .done b

/-! ### Correctness -/

theorem iter_trans {α : Type u} (f : α → α) {c1 c2 c3 : α} {n1 n2 : ℕ}
    (h1 : f^[n1] c1 = c2) (h2 : f^[n2] c2 = c3) : f^[n1 + n2] c1 = c3 := by
  rw [Nat.add_comm, Function.iterate_add_apply, h1, h2]

/-- The loop over midpoints, started at index `i`, returns the disjunction over
the candidates at positions `≥ i`. -/
theorem tryFrom_evals (E : V → V → Bool) (all : List V) (k : ℕ) (u v : V)
    (IH : ∀ (u' v' : V) (st' : List (Frame V)),
      ∃ n, (step E all)^[n] (.call k u' v' st') = .ret (sreach E all k u' v') st') :
    ∀ (d i : ℕ), all.length - i ≤ d → ∀ st : List (Frame V),
      ∃ n, (step E all)^[n] (tryFrom all k u v i st) =
        .ret ((all.drop i).any (fun m => sreach E all k u m && sreach E all k m v)) st := by
  intro d
  induction d with
  | zero =>
      intro i hi st
      have hlen : all.length ≤ i := by omega
      have hnone : all[i]? = none := List.getElem?_eq_none hlen
      have hdrop : all.drop i = [] := List.drop_eq_nil_of_le hlen
      exact ⟨0, by simp [tryFrom, hnone, hdrop]⟩
  | succ d ih =>
      intro i hi st
      by_cases hlt : i < all.length
      · set m := all[i] with hmdef
        have hgi : all[i]? = some m := List.getElem?_eq_getElem hlt
        have hdrop : all.drop i = m :: all.drop (i + 1) := List.drop_eq_getElem_cons hlt
        have hstart : tryFrom all k u v i st = Cfg.call k u m (.mid1 k u v i m :: st) := by
          simp [tryFrom, hgi]
        obtain ⟨n1, hn1⟩ := IH u m (.mid1 k u v i m :: st)
        by_cases h1 : sreach E all k u m = true
        · obtain ⟨n2, hn2⟩ := IH m v (.mid2 k u v i m :: st)
          have e2 : (step E all)^[1] (Cfg.ret (sreach E all k u m) (.mid1 k u v i m :: st))
              = Cfg.call k m v (.mid2 k u v i m :: st) := by rw [h1]; rfl
          by_cases h2 : sreach E all k m v = true
          · have e4 : (step E all)^[1] (Cfg.ret (sreach E all k m v) (.mid2 k u v i m :: st))
                = Cfg.ret true st := by rw [h2]; rfl
            refine ⟨n1 + 1 + n2 + 1, ?_⟩
            rw [hstart]
            have := iter_trans (step E all) (iter_trans (step E all)
              (iter_trans (step E all) hn1 e2) hn2) e4
            rw [this]
            simp [hdrop, h1, h2]
          · simp only [Bool.not_eq_true] at h2
            obtain ⟨n3, hn3⟩ := ih (i + 1) (by omega) st
            have e4 : (step E all)^[1] (Cfg.ret (sreach E all k m v) (.mid2 k u v i m :: st))
                = tryFrom all k u v (i + 1) st := by rw [h2]; rfl
            refine ⟨n1 + 1 + n2 + 1 + n3, ?_⟩
            rw [hstart]
            have := iter_trans (step E all) (iter_trans (step E all) (iter_trans (step E all)
              (iter_trans (step E all) hn1 e2) hn2) e4) hn3
            rw [this, hdrop]
            simp [h2]
        · simp only [Bool.not_eq_true] at h1
          obtain ⟨n3, hn3⟩ := ih (i + 1) (by omega) st
          have e2 : (step E all)^[1] (Cfg.ret (sreach E all k u m) (.mid1 k u v i m :: st))
              = tryFrom all k u v (i + 1) st := by rw [h1]; rfl
          refine ⟨n1 + 1 + n3, ?_⟩
          rw [hstart]
          have := iter_trans (step E all) (iter_trans (step E all) hn1 e2) hn3
          rw [this, hdrop]
          simp [h1]
      · push_neg at hlt
        have hnone : all[i]? = none := List.getElem?_eq_none hlt
        have hdrop : all.drop i = [] := List.drop_eq_nil_of_le hlt
        exact ⟨0, by simp [tryFrom, hnone, hdrop]⟩

/-- The machine evaluates a call correctly: from `call k u v st` it returns
`sreach E all k u v` on the same stack. -/
theorem call_evals (E : V → V → Bool) (all : List V) :
    ∀ (k : ℕ) (u v : V) (st : List (Frame V)),
      ∃ n, (step E all)^[n] (.call k u v st) = .ret (sreach E all k u v) st := by
  intro k
  induction k with
  | zero => exact fun u v st => ⟨1, rfl⟩
  | succ k ih =>
      intro u v st
      obtain ⟨n, hn⟩ :=
        tryFrom_evals E all k u v (fun u' v' st' => ih u' v' st') all.length 0 (by omega) st
      refine ⟨1 + n, ?_⟩
      have h0 : (step E all)^[1] (Cfg.call (k + 1) u v st) = tryFrom all k u v 0 st := rfl
      have := iter_trans (step E all) h0 hn
      rw [this]
      simp [sreach]

/-- Running the machine from the initial configuration produces the answer. -/
theorem run_call (E : V → V → Bool) (all : List V) (K : ℕ) (u v : V) :
    ∃ n, (step E all)^[n] (.call K u v []) = .done (sreach E all K u v) := by
  obtain ⟨n, hn⟩ := call_evals E all K u v []
  exact ⟨n + 1, iter_trans (step E all) hn rfl⟩

/-! ### The space bound: the stack never exceeds `K` frames -/

/-- Levels increase by one going down the stack. -/
def StackChain : List (Frame V) → Prop
  | [] => True
  | f :: st => (∀ g ∈ st.head?, g.level = f.level + 1) ∧ StackChain st

/-- The invariant maintained by a run started at level `K`. -/
def Inv (K : ℕ) : Cfg V → Prop
  | .call k _ _ st => k + st.length = K ∧ StackChain st ∧ ∀ f ∈ st.head?, f.level = k
  | .ret _ st => st.length ≤ K ∧ StackChain st ∧ ∀ f ∈ st.head?, f.level + st.length = K
  | .done _ => True

omit [DecidableEq V] in
theorem inv_init (K : ℕ) (u v : V) : Inv K (Cfg.call K u v ([] : List (Frame V))) :=
  ⟨by simp, trivial, by simp⟩

omit [DecidableEq V] in
theorem inv_tryFrom {all : List V} {K k : ℕ} {u v : V}
    {st : List (Frame V)} (i : ℕ)
    (hlen : k + st.length + 1 = K) (hchain : StackChain st)
    (hhead : ∀ f ∈ st.head?, f.level = k + 1) :
    Inv K (tryFrom all k u v i st) := by
  unfold tryFrom
  rcases hgi : all[i]? with _ | m
  · refine ⟨by omega, hchain, ?_⟩
    intro f hf
    have := hhead f hf
    omega
  · refine ⟨by simp; omega, ⟨?_, hchain⟩, by simp⟩
    intro g hg
    simpa using hhead g hg

theorem inv_step (E : V → V → Bool) (all : List V) (K : ℕ) (c : Cfg V) (h : Inv K c) :
    Inv K (step E all c) := by
  match c with
  | .call 0 u v st =>
      obtain ⟨hlen, hchain, hhead⟩ := h
      refine ⟨by omega, hchain, ?_⟩
      intro f hf
      have := hhead f hf
      omega
  | .call (k + 1) u v st =>
      obtain ⟨hlen, hchain, hhead⟩ := h
      exact inv_tryFrom (all := all) 0 (by omega) hchain hhead
  | .ret b [] => trivial
  | .ret b (.mid1 k u v i m :: st) =>
      obtain ⟨hlen, hchain, hhead⟩ := h
      have hh : k + (st.length + 1) = K := by
        have := hhead (Frame.mid1 k u v i m) (by simp)
        simpa using this
      obtain ⟨hst, hchain'⟩ := hchain
      simp only [Frame.level_mid1] at hst
      by_cases hb : b = true
      · subst hb
        refine ⟨?_, ⟨?_, hchain'⟩, ?_⟩
        · simp only [List.length_cons]; omega
        · intro g hg; simpa using hst g hg
        · intro f hf
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hf
          subst hf
          simp
      · simp only [Bool.not_eq_true] at hb
        subst hb
        exact inv_tryFrom (all := all) (i + 1) (by omega)
          hchain' hst
  | .ret b (.mid2 k u v i m :: st) =>
      obtain ⟨hlen, hchain, hhead⟩ := h
      have hh : k + (st.length + 1) = K := by
        have := hhead (Frame.mid2 k u v i m) (by simp)
        simpa using this
      obtain ⟨hst, hchain'⟩ := hchain
      simp only [Frame.level_mid2] at hst
      by_cases hb : b = true
      · subst hb
        refine ⟨by omega, hchain', ?_⟩
        intro g hg
        have := hst g hg
        omega
      · simp only [Bool.not_eq_true] at hb
        subst hb
        exact inv_tryFrom (all := all) (i + 1) (by omega) hchain' hst
  | .done b => trivial

theorem inv_iterate (E : V → V → Bool) (all : List V) (K : ℕ) (c : Cfg V) (h : Inv K c) (n : ℕ) :
    Inv K ((step E all)^[n] c) := by
  induction n generalizing c with
  | zero => simpa using h
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih _ (inv_step E all K c h)

omit [DecidableEq V] in
theorem stack_length_le_of_inv {K : ℕ} {c : Cfg V} (h : Inv K c) : c.stack.length ≤ K := by
  match c with
  | .call k u v st =>
      have h1 := h.1
      show st.length ≤ K
      omega
  | .ret b st => exact h.1
  | .done b => simp [Cfg.stack]

/-- **Space bound.**  Every configuration reachable from the initial
configuration `call K u v []` carries at most `K` stack frames. -/
theorem stack_length_le (E : V → V → Bool) (all : List V) (K : ℕ) (u v : V) (n : ℕ) :
    ((step E all)^[n] (Cfg.call K u v [])).stack.length ≤ K :=
  stack_length_le_of_inv (inv_iterate E all K _ (inv_init K u v) n)

/-! ### Every frame stores small data -/

/-- Second invariant: every frame on the stack has a recursion level `< K` and a
candidate index pointing into the vertex list. -/
def Inv2 (K : ℕ) (all : List V) (c : Cfg V) : Prop :=
  ∀ f ∈ c.stack, f.level < K ∧ f.idx < all.length

omit [DecidableEq V] in
theorem inv2_tryFrom {all : List V} {K k : ℕ} {u v : V} {st : List (Frame V)} (i : ℕ)
    (hk : k < K) (hst : ∀ f ∈ st, f.level < K ∧ f.idx < all.length) :
    Inv2 K all (tryFrom all k u v i st) := by
  unfold Inv2 tryFrom
  by_cases hlt : i < all.length
  · rw [List.getElem?_eq_getElem hlt]
    intro f hf
    simp only [Cfg.stack_call, List.mem_cons] at hf
    rcases hf with hf | hf
    · subst hf; exact ⟨by simpa using hk, by simpa using hlt⟩
    · exact hst f hf
  · push_neg at hlt
    rw [List.getElem?_eq_none hlt]
    simpa using hst

theorem inv2_step (E : V → V → Bool) (all : List V) (K : ℕ) (c : Cfg V)
    (h : Inv K c) (h2 : Inv2 K all c) : Inv2 K all (step E all c) := by
  match c with
  | .call 0 u v st => exact h2
  | .call (k + 1) u v st =>
      have hlen := h.1
      exact inv2_tryFrom 0 (by omega) h2
  | .ret b [] =>
      show Inv2 K all (Cfg.done b)
      intro f hf; simp at hf
  | .ret b (.mid1 k u v i m :: st) =>
      have hf0 := h2 (Frame.mid1 k u v i m) (by simp)
      have hst : ∀ f ∈ st, f.level < K ∧ f.idx < all.length := fun f hf =>
        h2 f (by simp [hf])
      by_cases hb : b = true
      · subst hb
        show Inv2 K all (Cfg.call k m v (Frame.mid2 k u v i m :: st))
        intro f hf
        simp only [Cfg.stack_call, List.mem_cons] at hf
        rcases hf with hf | hf
        · subst hf; simpa using hf0
        · exact hst f hf
      · simp only [Bool.not_eq_true] at hb
        subst hb
        exact inv2_tryFrom (i + 1) hf0.1 hst
  | .ret b (.mid2 k u v i m :: st) =>
      have hf0 := h2 (Frame.mid2 k u v i m) (by simp)
      have hst : ∀ f ∈ st, f.level < K ∧ f.idx < all.length := fun f hf =>
        h2 f (by simp [hf])
      by_cases hb : b = true
      · subst hb
        show Inv2 K all (Cfg.ret true st)
        exact fun f hf => hst f (by simpa using hf)
      · simp only [Bool.not_eq_true] at hb
        subst hb
        exact inv2_tryFrom (i + 1) hf0.1 hst
  | .done b =>
      show Inv2 K all (Cfg.done b)
      intro f hf; simp at hf

theorem inv2_iterate (E : V → V → Bool) (all : List V) (K : ℕ) (c : Cfg V)
    (h : Inv K c) (h2 : Inv2 K all c) (n : ℕ) : Inv2 K all ((step E all)^[n] c) := by
  induction n generalizing c with
  | zero => simpa using h2
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih _ (inv_step E all K c h) (inv2_step E all K c h h2)

/-- Every frame reachable in a run started at level `K` stores a level `< K` and
an index into the vertex list. -/
theorem frames_small (E : V → V → Bool) (all : List V) (K : ℕ) (u v : V) (n : ℕ) :
    ∀ f ∈ ((step E all)^[n] (Cfg.call K u v [])).stack,
      f.level < K ∧ f.idx < all.length :=
  inv2_iterate E all K _ (inv_init K u v) (by intro f hf; simp at hf) n

/-! ### The cost model

A frame consists of a recursion level `< K`, three vertices (`u`, `v` and the
current midpoint `m`), a loop index `< N` (where `N` is the number of vertices)
and a one-bit tag distinguishing `mid1` from `mid2`.  Writing all components in
binary, a frame occupies `frameWidth K N` bits. -/

/-- Number of bits occupied by one stack frame. -/
def frameWidth (K N : ℕ) : ℕ := Nat.clog 2 K + 4 * Nat.clog 2 N + 1

/-- Number of bits of memory used by a configuration. -/
def Cfg.bits (K N : ℕ) (c : Cfg V) : ℕ := c.stack.length * frameWidth K N

/-- **The space bound in bits.** -/
theorem bits_le (E : V → V → Bool) (all : List V) (K N : ℕ) (u v : V) (n : ℕ) :
    ((step E all)^[n] (Cfg.call K u v [])).bits K N ≤ K * frameWidth K N :=
  Nat.mul_le_mul_right _ (stack_length_le E all K u v n)

end Savitch
end CS

/-
Space bounded nondeterministic Turing machines.

A machine has a finite control, a read-only input tape holding the input word
`x : List Bool` (position `|x|` reads the end marker `none`), and a read/write
work tape.  A machine *running in space `s`* has `s + 1` work cells available;
this is the usual definition of a space bounded computation, where exceeding
the bound is forbidden.
-/
import RequestProject.StackMachine

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace CS

/-- Head movement. -/
inductive Dir where
  | left | stay | right
  deriving DecidableEq

/-- Move a head position inside a tape of `k + 1` cells; the head stays put at
the two ends. -/
def Dir.move {k : ℕ} : Dir → Fin (k + 1) → Fin (k + 1)
  | .left, p => ⟨p.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) p.isLt⟩
  | .stay, p => p
  | .right, p => if h : p.val + 1 < k + 1 then ⟨p.val + 1, h⟩ else p

/-- A nondeterministic Turing machine with a read-only input tape (over `Bool`)
and a read/write work tape (over `Γ`). -/
structure NTM where
  /-- The finite set of control states. -/
  Q : Type
  /-- The finite work-tape alphabet. -/
  Γ : Type
  [instQ : Fintype Q]
  [instQd : DecidableEq Q]
  [instG : Fintype Γ]
  [instGd : DecidableEq Γ]
  /-- The blank work-tape symbol. -/
  blank : Γ
  /-- The initial control state. -/
  start : Q
  /-- The accepting control state. -/
  acc : Q
  /-- The transition table: from a state, the symbol scanned on the input tape
  (`none` at the end marker) and the symbol scanned on the work tape, a finite
  list of possible successors (new state, symbol written, input head move,
  work head move). -/
  δ : Q → Option Bool → Γ → List (Q × Γ × Dir × Dir)

attribute [instance] NTM.instQ NTM.instQd NTM.instG NTM.instGd

/-- A configuration of `M` on an input of length `n` running in space `s`:
control state, input head position, work tape contents, work head position. -/
abbrev Conf (M : NTM) (n s : ℕ) : Type :=
  M.Q × Fin (n + 1) × (Fin (s + 1) → M.Γ) × Fin (s + 1)

/-- The initial configuration. -/
def initConf (M : NTM) (n s : ℕ) : Conf M n s :=
  (M.start, ⟨0, Nat.succ_pos n⟩, fun _ => M.blank, ⟨0, Nat.succ_pos s⟩)

/-- The one-step relation of `M` on input `x`, as a decidable predicate. -/
def stepB (M : NTM) (x : List Bool) {n s : ℕ} (c c' : Conf M n s) : Bool :=
  (M.δ c.1 x[c.2.1.val]? (c.2.2.1 c.2.2.2)).any fun t =>
    decide (c' = (t.1, t.2.2.1.move c.2.1,
      Function.update c.2.2.1 c.2.2.2 t.2.1, t.2.2.2.move c.2.2.2))

/-- `M` accepts `x` in space `s` if some accepting configuration is reachable
from the initial configuration. -/
def NTM.AcceptsIn (M : NTM) (s : ℕ) (x : List Bool) : Prop :=
  ∃ c : Conf M x.length s,
    Relation.ReflTransGen (fun a b => stepB M x a b = true) (initConf M x.length s) c ∧
      c.1 = M.acc

/-- `NSPACE f` : the languages accepted by a nondeterministic Turing machine
running in space `f`. -/
def NSPACE (f : ℕ → ℕ) : Set (Set (List Bool)) :=
  { L | ∃ M : NTM, ∀ x : List Bool, x ∈ L ↔ M.AcceptsIn (f x.length) x }

theorem card_conf (M : NTM) (n s : ℕ) :
    Fintype.card (Conf M n s)
      = Fintype.card M.Q * ((n + 1) * (Fintype.card M.Γ ^ (s + 1) * (s + 1))) := by
  simp [Conf, Fintype.card_prod, Fintype.card_fun]

end CS

/-
Bounded reachability in a (finite) directed graph.

This file develops the elementary theory of "reachable in at most `n` steps",
the halving identity that underlies Savitch's algorithm, and the fact that in a
finite graph reachability is the same as reachability in at most `card V` steps.
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace CS

universe u

variable {V : Type u}

/-- `reachLe E n u v` : `v` can be reached from `u` by at most `n` `E`-steps. -/
def reachLe (E : V → V → Prop) : ℕ → V → V → Prop
  | 0, u, v => u = v
  | n + 1, u, v => reachLe E n u v ∨ ∃ w, reachLe E n u w ∧ E w v

theorem reachLe_zero {E : V → V → Prop} {u v : V} : reachLe E 0 u v ↔ u = v := Iff.rfl

theorem reachLe_refl (E : V → V → Prop) (n : ℕ) (u : V) : reachLe E n u u := by
  induction n with
  | zero => rfl
  | succ n ih => exact Or.inl ih

theorem reachLe_mono {E : V → V → Prop} {m n : ℕ} (h : m ≤ n) {u v : V}
    (huv : reachLe E m u v) : reachLe E n u v := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.le_zero.1 h
      subst hm; exact huv
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hm | hm
      · exact Or.inl (ih (by omega))
      · have : m = n + 1 := le_antisymm h hm
        subst this; exact huv

theorem reachLe_succ_of_step {E : V → V → Prop} {n : ℕ} {u w v : V}
    (h : reachLe E n u w) (hs : E w v) : reachLe E (n + 1) u v :=
  Or.inr ⟨w, h, hs⟩

/-- Composition: a walk of length `≤ m + n` splits as a walk of length `≤ m`
followed by a walk of length `≤ n`. -/
theorem reachLe_add {E : V → V → Prop} (m n : ℕ) (u v : V) :
    reachLe E (m + n) u v ↔ ∃ w, reachLe E m u w ∧ reachLe E n w v := by
  induction n generalizing v with
  | zero =>
      constructor
      · intro h; exact ⟨v, h, rfl⟩
      · rintro ⟨w, hw, rfl⟩; simpa using hw
  | succ n ih =>
      constructor
      · intro h
        rcases h with h | ⟨z, hz, hzv⟩
        · obtain ⟨w, hw1, hw2⟩ := (ih v).1 h
          exact ⟨w, hw1, Or.inl hw2⟩
        · obtain ⟨w, hw1, hw2⟩ := (ih z).1 hz
          exact ⟨w, hw1, Or.inr ⟨z, hw2, hzv⟩⟩
      · rintro ⟨w, hw1, hw2⟩
        rcases hw2 with h | ⟨z, hz, hzv⟩
        · exact Or.inl ((ih v).2 ⟨w, hw1, h⟩)
        · exact Or.inr ⟨z, (ih z).2 ⟨w, hw1, hz⟩, hzv⟩

/-- The halving identity behind Savitch's algorithm. -/
theorem reachLe_two_pow_succ {E : V → V → Prop} (k : ℕ) (u v : V) :
    reachLe E (2 ^ (k + 1)) u v ↔
      ∃ w, reachLe E (2 ^ k) u w ∧ reachLe E (2 ^ k) w v := by
  have h : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
  rw [h, reachLe_add]

theorem reachLe_reflTransGen {E : V → V → Prop} {n : ℕ} {u v : V}
    (h : reachLe E n u v) : Relation.ReflTransGen E u v := by
  induction n generalizing v with
  | zero => cases h; exact Relation.ReflTransGen.refl
  | succ n ih =>
      rcases h with h | ⟨w, hw, hwv⟩
      · exact ih h
      · exact (ih hw).tail hwv

/-! ### Reachability in a finite graph is bounded reachability -/

section Finite

variable [Fintype V]

open scoped Classical in
/-- The finset of vertices reachable from `u` in at most `n` steps. -/
noncomputable def reachSet (E : V → V → Prop) (u : V) (n : ℕ) : Finset V :=
  Finset.univ.filter (fun v => reachLe E n u v)

theorem mem_reachSet {E : V → V → Prop} {u : V} {n : ℕ} {v : V} :
    v ∈ reachSet E u n ↔ reachLe E n u v := by
  classical
  simp [reachSet]

theorem reachSet_subset {E : V → V → Prop} {u : V} {m n : ℕ} (h : m ≤ n) :
    reachSet E u m ⊆ reachSet E u n := by
  intro v hv
  exact mem_reachSet.2 (reachLe_mono h (mem_reachSet.1 hv))

/-- If the reachable-set stops growing at step `n`, it never grows again. -/
theorem reachSet_stable {E : V → V → Prop} {u : V} {n : ℕ}
    (h : reachSet E u (n + 1) = reachSet E u n) (m : ℕ) :
    reachSet E u (n + m) = reachSet E u n := by
  induction m with
  | zero => rfl
  | succ m ih =>
      apply Finset.Subset.antisymm
      · intro v hv
        have hv' : reachLe E (n + m + 1) u v := mem_reachSet.1 hv
        rcases hv' with hh | ⟨w, hw, hwv⟩
        · exact ih ▸ mem_reachSet.2 hh
        · have hwn : w ∈ reachSet E u n := ih ▸ mem_reachSet.2 hw
          have : v ∈ reachSet E u (n + 1) := by
            exact mem_reachSet.2 (reachLe_succ_of_step (mem_reachSet.1 hwn) hwv)
          rwa [h] at this
      · exact reachSet_subset (by omega)

theorem card_reachSet_lt {E : V → V → Prop} {u : V} {n : ℕ}
    (h : reachSet E u (n + 1) ≠ reachSet E u n) :
    (reachSet E u n).card < (reachSet E u (n + 1)).card := by
  have hsub : reachSet E u n ⊆ reachSet E u (n + 1) := reachSet_subset (by omega)
  exact Finset.card_lt_card (lt_of_le_of_ne (Finset.le_iff_subset.2 hsub) (Ne.symm h))

theorem card_le_card_reachSet {E : V → V → Prop} {u : V} (n : ℕ)
    (h : ∀ m < n, reachSet E u (m + 1) ≠ reachSet E u m) :
    n + 1 ≤ (reachSet E u n).card := by
  induction n with
  | zero =>
      have : u ∈ reachSet E u 0 := mem_reachSet.2 rfl
      exact Finset.card_pos.2 ⟨u, this⟩
  | succ n ih =>
      have h1 : n + 1 ≤ (reachSet E u n).card := ih (fun m hm => h m (by omega))
      have h2 := card_reachSet_lt (h n (by omega))
      omega

/-- In a finite graph, reachability implies reachability in at most `card V` steps. -/
theorem reachLe_card_of_reflTransGen {E : V → V → Prop} {u v : V}
    (h : Relation.ReflTransGen E u v) : reachLe E (Fintype.card V) u v := by
  classical
  -- first: `reachLe` holds for some `n`
  have hex : ∃ n, reachLe E n u v := by
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail hab hbc ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, reachLe_succ_of_step hn hbc⟩
  obtain ⟨n, hn⟩ := hex
  set N := Fintype.card V with hN
  by_cases hstab : ∃ m < N, reachSet E u (m + 1) = reachSet E u m
  · obtain ⟨m, hmN, hm⟩ := hstab
    rcases Nat.le_total n m with hnm | hnm
    · exact reachLe_mono (le_trans hnm (le_of_lt hmN)) hn
    · have : v ∈ reachSet E u (m + (n - m)) := by
        have : m + (n - m) = n := by omega
        rw [this]; exact mem_reachSet.2 hn
      rw [reachSet_stable hm] at this
      exact reachLe_mono (le_of_lt hmN) (mem_reachSet.1 this)
  · push_neg at hstab
    have := card_le_card_reachSet (E := E) (u := u) N (fun m hm => hstab m hm)
    have hcard : (reachSet E u N).card ≤ N := by
      simpa [hN] using Finset.card_le_univ (reachSet E u N)
    omega

end Finite

/-! ### The Boolean divide-and-conquer specification -/

section Spec

variable [DecidableEq V]

/-- `sreach E all k u v` decides whether `v` is reachable from `u` in at most
`2 ^ k` steps, by the middle-first recursion. -/
def sreach (E : V → V → Bool) (all : List V) : ℕ → V → V → Bool
  | 0, u, v => decide (u = v) || E u v
  | k + 1, u, v => all.any (fun m => sreach E all k u m && sreach E all k m v)

theorem sreach_iff (E : V → V → Bool) (all : List V) (hall : ∀ v : V, v ∈ all)
    (k : ℕ) (u v : V) :
    sreach E all k u v = true ↔ reachLe (fun a b => E a b = true) (2 ^ k) u v := by
  induction k generalizing u v with
  | zero =>
      simp only [sreach, Bool.or_eq_true, decide_eq_true_eq, pow_zero]
      constructor
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr ⟨u, rfl, h⟩
      · rintro (h | ⟨w, hw, hwv⟩)
        · exact Or.inl h
        · cases hw; exact Or.inr hwv
  | succ k ih =>
      rw [reachLe_two_pow_succ]
      simp only [sreach, List.any_eq_true, Bool.and_eq_true]
      constructor
      · rintro ⟨m, _, h1, h2⟩
        exact ⟨m, (ih u m).1 h1, (ih m v).1 h2⟩
      · rintro ⟨m, h1, h2⟩
        exact ⟨m, hall m, (ih u m).2 h1, (ih m v).2 h2⟩

end Spec

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

