/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (it uses only the Lean 4 core library), so that the
required header comment above can literally be the first thing in the file.
-/

namespace CS

/-! ## Counting -/

/-- `HasCard α N` says that the type `α` embeds into `Fin N`; i.e. `α` has at most `N`
elements, so an element of `α` can be stored in `⌈log₂ N⌉` bits. -/
def HasCard (α : Type) (N : Nat) : Prop := ∃ f : α → Fin N, Function.Injective f

theorem hasCard_fin (n : Nat) : HasCard (Fin n) n := ⟨id, fun _ _ h => h⟩

theorem hasCard_bool : HasCard Bool 2 :=
  ⟨fun b => if b then ⟨1, by omega⟩ else ⟨0, by omega⟩, by
    intro a b h
    cases a <;> cases b <;> simp_all⟩

theorem hasCard_prod {α β : Type} {N M : Nat} (hα : HasCard α N) (hβ : HasCard β M) :
    HasCard (α × β) (N * M) := by
  obtain ⟨f, hf⟩ := hα
  obtain ⟨g, hg⟩ := hβ
  refine ⟨fun p => ⟨(g p.2).1 + M * (f p.1).1, ?_⟩, ?_⟩
  · have hx : (f p.1).1 < N := (f p.1).2
    have hy : (g p.2).1 < M := (g p.2).2
    have h1 : M * ((f p.1).1 + 1) ≤ M * N := Nat.mul_le_mul_left M hx
    have h2 : M * ((f p.1).1 + 1) = M * (f p.1).1 + M := by
      rw [Nat.mul_add, Nat.mul_one]
    have : N * M = M * N := Nat.mul_comm _ _
    omega
  · rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    have h' : (g b1).1 + M * (f a1).1 = (g b2).1 + M * (f a2).1 := by
      simpa using congrArg Fin.val h
    have hy1 : (g b1).1 < M := (g b1).2
    have hy2 : (g b2).1 < M := (g b2).2
    have hM : 0 < M := Nat.lt_of_le_of_lt (Nat.zero_le _) hy1
    have e1 : ((g b1).1 + M * (f a1).1) % M = (g b1).1 % M := Nat.add_mul_mod_self_left _ _ _
    have e2 : ((g b2).1 + M * (f a2).1) % M = (g b2).1 % M := Nat.add_mul_mod_self_left _ _ _
    have hb : (g b1).1 = (g b2).1 := by
      have e3 : (g b1).1 % M = (g b2).1 % M := by rw [← e1, ← e2, h']
      rwa [Nat.mod_eq_of_lt hy1, Nat.mod_eq_of_lt hy2] at e3
    have ha : (f a1).1 = (f a2).1 := by
      have : M * (f a1).1 = M * (f a2).1 := by omega
      exact Nat.eq_of_mul_eq_mul_left hM this
    have ha' : a1 = a2 := hf (Fin.ext ha)
    have hb' : b1 = b2 := hg (Fin.ext hb)
    simp [ha', hb']

/-! ## Undirected graphs presented by rotation maps -/

/-- An undirected `d`-regular (multi)graph on the vertex set `Fin n`, presented by its
*rotation map*: `rot (v, a) = (w, b)` means that the `a`-th edge out of `v` leads to `w`,
and arrives there as the `b`-th edge of `w`.  Involutivity of `rot` is exactly the
statement that the graph is undirected. -/
structure RotGraph (n d : Nat) where
  rot : Fin n × Fin d → Fin n × Fin d
  rot_involutive : ∀ x, rot (rot x) = x

namespace RotGraph

/-- Following the edge labelled `a` out of the vertex `v`. -/
def step1 {n d : Nat} (G : RotGraph n d) (v : Fin n) (a : Fin d) : Fin n := (G.rot (v, a)).1

/-- Adjacency in the graph described by the rotation map. -/
def Adj {n d : Nat} (G : RotGraph n d) (u v : Fin n) : Prop := ∃ a : Fin d, G.step1 u a = v

/-- The graph is undirected: adjacency is symmetric. -/
theorem adj_symm {n d : Nat} (G : RotGraph n d) {u v : Fin n} (h : G.Adj u v) : G.Adj v u := by
  obtain ⟨a, ha⟩ := h
  refine ⟨(G.rot (u, a)).2, ?_⟩
  have h2 := G.rot_involutive (u, a)
  have h3 : (v, (G.rot (u, a)).2) = G.rot (u, a) := by
    rw [← ha]; rfl
  show (G.rot (v, (G.rot (u, a)).2)).1 = u
  rw [h3, h2]

/-- The endpoint of the walk starting at `v` and following the edge labels in `l`. -/
def walk {n d : Nat} (G : RotGraph n d) (v : Fin n) : List (Fin d) → Fin n
  | [] => v
  | a :: l => G.walk (G.step1 v a) l

/-- Connectivity: the reflexive transitive closure of adjacency. -/
inductive Reach {n d : Nat} (G : RotGraph n d) : Fin n → Fin n → Prop
  | refl (v : Fin n) : Reach G v v
  | tail {u v w : Fin n} : Reach G u v → G.Adj v w → Reach G u w

theorem reach_trans {n d : Nat} (G : RotGraph n d) {a b c : Fin n}
    (h1 : G.Reach a b) (h2 : G.Reach b c) : G.Reach a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hadj ih => exact Reach.tail ih hadj

theorem reach_walk {n d : Nat} (G : RotGraph n d) (s : Fin n) (l : List (Fin d)) :
    G.Reach s (G.walk s l) := by
  induction l generalizing s with
  | nil => exact Reach.refl _
  | cons a l ih =>
      have h1 : G.Reach s (G.step1 s a) := Reach.tail (Reach.refl s) ⟨a, rfl⟩
      exact G.reach_trans h1 (ih _)

theorem walk_append {n d : Nat} (G : RotGraph n d) (s : Fin n) (l : List (Fin d)) (a : Fin d) :
    G.walk s (l ++ [a]) = G.step1 (G.walk s l) a := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => exact ih _

theorem reach_iff_exists_walk {n d : Nat} (G : RotGraph n d) {s t : Fin n} :
    G.Reach s t ↔ ∃ l : List (Fin d), G.walk s l = t := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl⟩
    | tail _ hadj ih =>
        obtain ⟨l, hl⟩ := ih
        obtain ⟨a, ha⟩ := hadj
        exact ⟨l ++ [a], by rw [G.walk_append, hl, ha]⟩
  · rintro ⟨l, rfl⟩
    exact G.reach_walk s l

end RotGraph

/-! ## A space-bounded machine model with oracle access to the graph -/

/-- A deterministic machine with a finite memory (at most `size` configurations, i.e.
`⌈log₂ size⌉` bits of work space) that accesses the input graph only through its rotation
map: at each step it asks for the value of the rotation map at one point, determined by its
current memory contents, and updates its memory using the answer.  This is the standard
read-only/oracle formulation of a space-bounded algorithm; the space used is
`⌈log₂ size⌉` bits. -/
structure Machine (n d : Nat) where
  Mem : Type
  size : Nat
  card : HasCard Mem size
  init : Fin n → Fin n → Mem
  query : Mem → Fin n × Fin d
  update : Mem → Fin n × Fin d → Mem
  out : Mem → Bool
  time : Nat

/-- Iterating a function. -/
def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => f (iterate f k x)

/-- One computation step of the machine on the graph `G`. -/
def Machine.step {n d : Nat} (M : Machine n d) (G : RotGraph n d) (m : M.Mem) : M.Mem :=
  M.update m (G.rot (M.query m))

/-- The output of the machine on input `(G, s, t)`. -/
def Machine.result {n d : Nat} (M : Machine n d) (G : RotGraph n d) (s t : Fin n) : Bool :=
  M.out (iterate (M.step G) M.time (M.init s t))

/-! ## Digits -/

/-- The `i`-th digit of `c` in base `d`. -/
def digitF {d : Nat} (hd : 0 < d) (c i : Nat) : Fin d := ⟨c / d ^ i % d, Nat.mod_lt _ hd⟩

/-- The list of the first `i` digits of `c` in base `d` (least significant first). -/
def digitsList {d : Nat} (hd : 0 < d) (c : Nat) : Nat → List (Fin d)
  | 0 => []
  | i + 1 => digitF hd c 0 :: digitsList hd (c / d) i

theorem digitsList_length {d : Nat} (hd : 0 < d) (c i : Nat) :
    (digitsList hd c i).length = i := by
  induction i generalizing c with
  | zero => rfl
  | succ i ih => simp [digitsList, ih]

/-- Encoding a list of digits as a natural number (least significant digit first). -/
def encode {d : Nat} : List (Fin d) → Nat
  | [] => 0
  | a :: l => a.1 + d * encode l

theorem encode_lt {d : Nat} (hd : 0 < d) (l : List (Fin d)) : encode l < d ^ l.length := by
  induction l with
  | nil => simp [encode]
  | cons a l ih =>
      have ha : a.1 < d := a.2
      have h1 : d * encode l + d ≤ d * d ^ l.length := by
        have h := Nat.mul_le_mul_left d (Nat.succ_le_of_lt ih)
        rw [Nat.mul_succ] at h
        exact h
      have hpow : d ^ (a :: l).length = d * d ^ l.length := by
        simp [List.length_cons, Nat.pow_succ, Nat.mul_comm]
      show a.1 + d * encode l < d ^ (a :: l).length
      rw [hpow]
      omega

theorem digitsList_encode {d : Nat} (hd : 0 < d) (l : List (Fin d)) :
    digitsList hd (encode l) l.length = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have ha : a.1 < d := a.2
      have h0 : digitF hd (encode (a :: l)) 0 = a := by
        apply Fin.ext
        show (a.1 + d * encode l) / d ^ 0 % d = a.1
        rw [Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
      have h1 : encode (a :: l) / d = encode l := by
        show (a.1 + d * encode l) / d = encode l
        rw [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt ha, Nat.zero_add]
      show digitF hd (encode (a :: l)) 0 :: digitsList hd (encode (a :: l) / d) l.length
          = a :: l
      rw [h0, h1, ih]

/-! ## The algorithm -/

namespace RotGraph

/-- The walk from `s` following the first `k` digits of `c` in base `d` as edge labels. -/
def cwalk {n d : Nat} (G : RotGraph n d) (hd : 0 < d) (s : Fin n) (c : Nat) : Nat → Fin n
  | 0 => s
  | k + 1 => G.step1 (G.cwalk hd s c k) (digitF hd c k)

theorem cwalk_front {n d : Nat} (G : RotGraph n d) (hd : 0 < d) (s : Fin n) (c k : Nat) :
    G.cwalk hd s c (k + 1) = G.cwalk hd (G.step1 s (digitF hd c 0)) (c / d) k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      have hdig : digitF hd (c / d) k = digitF hd c (k + 1) := by
        apply Fin.ext
        show c / d / d ^ k % d = c / d ^ (k + 1) % d
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (d ^ k) d]
      show G.step1 (G.cwalk hd s c (k + 1)) (digitF hd c (k + 1))
          = G.step1 (G.cwalk hd (G.step1 s (digitF hd c 0)) (c / d) k) (digitF hd (c / d) k)
      rw [ih, hdig]

theorem cwalk_eq_walk {n d : Nat} (G : RotGraph n d) (hd : 0 < d) (s : Fin n) (c i : Nat) :
    G.cwalk hd s c i = G.walk s (digitsList hd c i) := by
  induction i generalizing s c with
  | zero => rfl
  | succ i ih =>
      rw [G.cwalk_front hd s c i, ih]
      rfl

end RotGraph

/-- Total number of steps of the algorithm: it tries all `d ^ D` label sequences of length
`D`, spending `D + 1` steps on each. -/
def Tm (d D : Nat) : Nat := d ^ D * (D + 1)

/-- Memory of the algorithm: the two endpoints `s`, `t`, a step counter, the current
vertex, and a flag recording whether `t` has been seen so far. -/
def memT (n d D : Nat) : Type := Fin n × Fin n × Fin (Tm d D + 1) × Fin n × Bool

/-- The oracle query made in a given memory state. -/
def qry {n d : Nat} (D : Nat) (hd : 0 < d) (m : memT n d D) : Fin n × Fin d :=
  (m.2.2.2.1, digitF hd (m.2.2.1.1 / (D + 1)) (m.2.2.1.1 % (D + 1)))

/-- The memory update, given the answer `x` to the query. -/
def upd {n d : Nat} (D : Nat) (m : memT n d D) (x : Fin n × Fin d) : memT n d D :=
  let j := m.2.2.1.1
  let j' : Fin (Tm d D + 1) := ⟨min (j + 1) (Tm d D), by omega⟩
  if j % (D + 1) = D then (m.1, m.2.1, j', m.1, m.2.2.2.2)
  else (m.1, m.2.1, j', x.1, m.2.2.2.2 || decide (x.1 = m.2.1))

/-- The machine implementing the algorithm: it enumerates all edge-label sequences of
length `D`, walking along each of them from `s` and checking whether `t` is ever reached. -/
def ustconMachine (n d D : Nat) (hd : 0 < d) : Machine n d where
  Mem := memT n d D
  size := n * (n * ((Tm d D + 1) * (n * 2)))
  card := hasCard_prod (hasCard_fin n)
    (hasCard_prod (hasCard_fin n)
      (hasCard_prod (hasCard_fin _) (hasCard_prod (hasCard_fin n) hasCard_bool)))
  init := fun s t => (s, t, ⟨0, by omega⟩, s, decide (s = t))
  query := qry D hd
  update := upd D
  out := fun m => m.2.2.2.2
  time := Tm d D

/-- The vertex visited at time `j`. -/
def vAt {n d : Nat} (G : RotGraph n d) (D : Nat) (hd : 0 < d) (s : Fin n) (j : Nat) : Fin n :=
  G.cwalk hd s (j / (D + 1)) (j % (D + 1))

theorem vAt_zero {n d : Nat} (G : RotGraph n d) (D : Nat) (hd : 0 < d) (s : Fin n) :
    vAt G D hd s 0 = s := rfl

theorem vAt_reset {n d : Nat} (G : RotGraph n d) (D : Nat) (hd : 0 < d) (s : Fin n) {j : Nat}
    (h : j % (D + 1) = D) : vAt G D hd s (j + 1) = s := by
  have hj : (D + 1) * (j / (D + 1)) + j % (D + 1) = j := Nat.div_add_mod j (D + 1)
  have hj' : j + 1 = (D + 1) * (j / (D + 1) + 1) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  have hmod : (j + 1) % (D + 1) = 0 := by rw [hj']; exact Nat.mul_mod_right _ _
  show G.cwalk hd s ((j + 1) / (D + 1)) ((j + 1) % (D + 1)) = s
  rw [hmod]
  rfl

theorem vAt_advance {n d : Nat} (G : RotGraph n d) (D : Nat) (hd : 0 < d) (s : Fin n) {j : Nat}
    (h : j % (D + 1) ≠ D) :
    vAt G D hd s (j + 1) =
      G.step1 (vAt G D hd s j) (digitF hd (j / (D + 1)) (j % (D + 1))) := by
  have hm : 0 < D + 1 := Nat.succ_pos D
  have hlt : j % (D + 1) < D + 1 := Nat.mod_lt _ hm
  have hj : (D + 1) * (j / (D + 1)) + j % (D + 1) = j := Nat.div_add_mod j (D + 1)
  have hj' : j + 1 = (j % (D + 1) + 1) + (D + 1) * (j / (D + 1)) := by omega
  have hmod : (j + 1) % (D + 1) = j % (D + 1) + 1 := by
    rw [hj', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hdiv : (j + 1) / (D + 1) = j / (D + 1) := by
    rw [hj', Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  show G.cwalk hd s ((j + 1) / (D + 1)) ((j + 1) % (D + 1)) = _
  rw [hmod, hdiv]
  rfl

/-- The invariant maintained by the machine along its run. -/
theorem run_invariant {n d : Nat} (G : RotGraph n d) (D : Nat) (hd : 0 < d) (s t : Fin n) :
    ∀ j : Nat, j ≤ Tm d D →
      ((iterate ((ustconMachine n d D hd).step G) j
          ((ustconMachine n d D hd).init s t) : memT n d D).1 = s ∧
       (iterate ((ustconMachine n d D hd).step G) j
          ((ustconMachine n d D hd).init s t) : memT n d D).2.1 = t ∧
       (iterate ((ustconMachine n d D hd).step G) j
          ((ustconMachine n d D hd).init s t) : memT n d D).2.2.1.1 = j ∧
       (iterate ((ustconMachine n d D hd).step G) j
          ((ustconMachine n d D hd).init s t) : memT n d D).2.2.2.1 = vAt G D hd s j ∧
       ((iterate ((ustconMachine n d D hd).step G) j
          ((ustconMachine n d D hd).init s t) : memT n d D).2.2.2.2 = true ↔
          ∃ k, k ≤ j ∧ vAt G D hd s k = t)) := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      show (decide (s = t) = true) ↔ _
      constructor
      · intro h
        exact ⟨0, Nat.le_refl _, by rw [vAt_zero]; exact of_decide_eq_true h⟩
      · rintro ⟨k, hk, hkt⟩
        have hk0 : k = 0 := Nat.le_zero.mp hk
        subst hk0
        rw [vAt_zero] at hkt
        simp [hkt]
  | succ j ih =>
      intro hj
      have hj' : j ≤ Tm d D := Nat.le_of_succ_le hj
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih hj'
      set m : memT n d D := iterate ((ustconMachine n d D hd).step G) j
        ((ustconMachine n d D hd).init s t) with hm
      have hstep : (iterate ((ustconMachine n d D hd).step G) (j + 1)
          ((ustconMachine n d D hd).init s t) : memT n d D)
          = upd D m (G.rot (qry D hd m)) := rfl
      have hjval : min (j + 1) (Tm d D) = j + 1 := by omega
      by_cases hcase : j % (D + 1) = D
      · have hupd : upd D m (G.rot (qry D hd m))
            = (m.1, m.2.1, (⟨min (j + 1) (Tm d D), by omega⟩ : Fin (Tm d D + 1)),
                m.1, m.2.2.2.2) := by
          show (if m.2.2.1.1 % (D + 1) = D then _ else _) = _
          rw [h3]
          simp [hcase]
        rw [hstep, hupd]
        refine ⟨h1, h2, by simpa using hjval, ?_, ?_⟩
        · show m.1 = vAt G D hd s (j + 1)
          rw [h1, vAt_reset G D hd s hcase]
        · show m.2.2.2.2 = true ↔ _
          rw [h5]
          constructor
          · rintro ⟨k, hk, hkt⟩; exact ⟨k, by omega, hkt⟩
          · rintro ⟨k, hk, hkt⟩
            rcases Nat.lt_or_ge k (j + 1) with hlt | hge
            · exact ⟨k, by omega, hkt⟩
            · have hkj : k = j + 1 := by omega
              subst hkj
              rw [vAt_reset G D hd s hcase] at hkt
              exact ⟨0, Nat.zero_le _, by rw [vAt_zero]; exact hkt⟩
      · have hq : qry D hd m = (vAt G D hd s j, digitF hd (j / (D + 1)) (j % (D + 1))) := by
          show (m.2.2.2.1, digitF hd (m.2.2.1.1 / (D + 1)) (m.2.2.1.1 % (D + 1))) = _
          rw [h3, h4]
        have hnext : (G.rot (qry D hd m)).1 = vAt G D hd s (j + 1) := by
          rw [hq, vAt_advance G D hd s hcase]
          rfl
        have hupd : upd D m (G.rot (qry D hd m))
            = (m.1, m.2.1, (⟨min (j + 1) (Tm d D), by omega⟩ : Fin (Tm d D + 1)),
                (G.rot (qry D hd m)).1,
                m.2.2.2.2 || decide ((G.rot (qry D hd m)).1 = m.2.1)) := by
          show (if m.2.2.1.1 % (D + 1) = D then _ else _) = _
          rw [h3]
          simp [hcase]
        rw [hstep, hupd]
        refine ⟨h1, h2, by simpa using hjval, hnext, ?_⟩
        show (m.2.2.2.2 || decide ((G.rot (qry D hd m)).1 = m.2.1)) = true ↔ _
        rw [h2, hnext]
        constructor
        · intro h
          rcases Bool.or_eq_true_iff.mp h with hA | hB
          · obtain ⟨k, hk, hkt⟩ := h5.mp hA
            exact ⟨k, by omega, hkt⟩
          · exact ⟨j + 1, Nat.le_refl _, of_decide_eq_true hB⟩
        · rintro ⟨k, hk, hkt⟩
          rcases Nat.lt_or_ge k (j + 1) with hlt | hge
          · have hA : m.2.2.2.2 = true := h5.mpr ⟨k, by omega, hkt⟩
            rw [hA]; rfl
          · have hkj : k = j + 1 := by omega
            subst hkj
            rw [decide_eq_true hkt]
            exact Bool.or_true _

/-- Correctness of the enumeration: the algorithm visits `t` iff there is a walk of length
at most `D` from `s` to `t`. -/
theorem exists_visit_iff {n d : Nat} (G : RotGraph n d) (D : Nat) (hd : 0 < d) (s t : Fin n) :
    (∃ k, k ≤ Tm d D ∧ vAt G D hd s k = t) ↔
      ∃ l : List (Fin d), l.length ≤ D ∧ G.walk s l = t := by
  constructor
  · rintro ⟨k, _, hk⟩
    refine ⟨digitsList hd (k / (D + 1)) (k % (D + 1)), ?_, ?_⟩
    · rw [digitsList_length]
      have hlt : k % (D + 1) < D + 1 := Nat.mod_lt _ (Nat.succ_pos D)
      omega
    · rw [← RotGraph.cwalk_eq_walk G hd s (k / (D + 1)) (k % (D + 1))]
      exact hk
  · rintro ⟨l, hlen, hl⟩
    refine ⟨l.length + (D + 1) * encode l, ?_, ?_⟩
    · have h1 : encode l < d ^ l.length := encode_lt hd l
      have h2 : d ^ l.length ≤ d ^ D := Nat.pow_le_pow_right hd hlen
      have h3 : (D + 1) * (encode l + 1) ≤ (D + 1) * d ^ D :=
        Nat.mul_le_mul_left _ (by omega)
      have h4 : (D + 1) * (encode l + 1) = (D + 1) * encode l + (D + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      have h5 : (D + 1) * d ^ D = Tm d D := Nat.mul_comm _ _
      omega
    · have hm : 0 < D + 1 := Nat.succ_pos D
      have hmod : (l.length + (D + 1) * encode l) % (D + 1) = l.length := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      have hdiv : (l.length + (D + 1) * encode l) / (D + 1) = encode l := by
        rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt (by omega), Nat.zero_add]
      show G.cwalk hd s ((l.length + (D + 1) * encode l) / (D + 1))
          ((l.length + (D + 1) * encode l) % (D + 1)) = t
      rw [hmod, hdiv, RotGraph.cwalk_eq_walk G hd s (encode l) l.length,
        digitsList_encode hd l]
      exact hl

/-!
## Main theorem

`CS.reingold_sl_l` below is a formalised statement that undirected `s`-`t` connectivity is
solvable in logarithmic space, in the following precise sense.

For a `d`-regular undirected graph on `n` vertices presented by a rotation map, all of
whose connected components have diameter at most `D`, there is a deterministic machine
which reads the graph only through its rotation map (one query per step), uses a memory
with only `2·n³·(d^D·(D+1)+1)` configurations, and decides connectivity of every pair
`s`, `t`.  When `d` is a constant and `D = O(log n)` — exactly the situation Reingold's
zig-zag transformation produces — the number of memory configurations is polynomial in
`n`, i.e. the machine works in space `O(log n)`, so undirected connectivity is in `L`.

This formalises the final phase of Reingold's algorithm: the deterministic
logarithmic-space enumeration of all short label sequences.  The preprocessing phase of
Reingold's proof, which turns an arbitrary undirected graph into a constant-degree graph
of logarithmic diameter by iterated zig-zag products, is *not* formalised here; the
bounded-diameter hypothesis `hdiam` below is what that phase supplies.
-/
theorem reingold_sl_l (n d D : Nat) (hd : 0 < d) :
    ∃ M : Machine n d,
      M.size = n * (n * ((d ^ D * (D + 1) + 1) * (n * 2))) ∧
      M.time = d ^ D * (D + 1) ∧
      ∀ G : RotGraph n d,
        (∀ s t : Fin n, G.Reach s t → ∃ l : List (Fin d), l.length ≤ D ∧ G.walk s l = t) →
        ∀ s t : Fin n, ((M.result G s t = true) ↔ G.Reach s t) := by
  refine ⟨ustconMachine n d D hd, rfl, rfl, ?_⟩
  intro G hdiam s t
  obtain ⟨-, -, -, -, h5⟩ := run_invariant G D hd s t (Tm d D) (Nat.le_refl _)
  have hres : ((ustconMachine n d D hd).result G s t = true) ↔
      ∃ k, k ≤ Tm d D ∧ vAt G D hd s k = t := h5
  rw [hres, exists_visit_iff G D hd s t]
  constructor
  · rintro ⟨l, -, hl⟩
    rw [← hl]
    exact G.reach_walk s l
  · intro h
    exact hdiam s t h

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

