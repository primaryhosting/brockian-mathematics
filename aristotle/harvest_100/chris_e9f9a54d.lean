/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-! ## Graphs presented by neighbour maps -/

variable {n D k : ℕ}

/-- `walk nbr v w j` is the vertex reached from `v` after following the first `j`
directions of the direction sequence `w` in the `D`-regular graph given by the
neighbour map `nbr`. -/
def walk (nbr : Fin n → Fin D → Fin n) (v : Fin n) (w : ℕ → Fin D) : ℕ → Fin n
  | 0 => v
  | j + 1 => nbr (walk nbr v w j) (w j)

/-- `t` is reachable from `s`. -/
def Reach (nbr : Fin n → Fin D → Fin n) (s t : Fin n) : Prop :=
  ∃ w : ℕ → Fin D, ∃ j : ℕ, walk nbr s w j = t

/-- `t` is reachable from `s` by a walk of length at most `k`. -/
def ReachWithin (nbr : Fin n → Fin D → Fin n) (s t : Fin n) (k : ℕ) : Prop :=
  ∃ w : ℕ → Fin D, ∃ j ≤ k, walk nbr s w j = t

theorem walk_congr (nbr : Fin n → Fin D → Fin n) (v : Fin n) (w w' : ℕ → Fin D) (j : ℕ)
    (h : ∀ x < j, w x = w' x) : walk nbr v w j = walk nbr v w' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [walk, ih (fun x hx => h x (by omega)), h j (by omega)]

theorem ReachWithin.mono {nbr : Fin n → Fin D → Fin n} {s t : Fin n} {k k' : ℕ}
    (h : ReachWithin nbr s t k) (hk : k ≤ k') : ReachWithin nbr s t k' := by
  obtain ⟨w, j, hj, hw⟩ := h
  exact ⟨w, j, hj.trans hk, hw⟩

theorem ReachWithin.reach {nbr : Fin n → Fin D → Fin n} {s t : Fin n} {k : ℕ}
    (h : ReachWithin nbr s t k) : Reach nbr s t := by
  obtain ⟨w, j, _, hw⟩ := h
  exact ⟨w, j, hw⟩

/-- Reachability along neighbour maps agrees with the reflexive-transitive closure of the
edge relation, i.e. with the usual notion of connectivity of the underlying graph. -/
theorem reach_iff_reflTransGen [NeZero D] (nbr : Fin n → Fin D → Fin n) (s t : Fin n) :
    Reach nbr s t ↔ Relation.ReflTransGen (fun u v => ∃ e, nbr u e = v) s t := by
  constructor
  · rintro ⟨w, j, rfl⟩
    induction j with
    | zero => exact Relation.ReflTransGen.refl
    | succ j ih => exact ih.tail ⟨w j, rfl⟩
  · intro h
    induction h with
    | refl => exact ⟨fun _ => (0 : Fin D), 0, rfl⟩
    | tail hu he ih =>
        obtain ⟨w, j, hw⟩ := ih
        obtain ⟨e, he⟩ := he
        refine ⟨Function.update w j e, j + 1, ?_⟩
        have hj : walk nbr s (Function.update w j e) j = walk nbr s w j := by
          refine walk_congr _ _ _ _ _ (fun x hx => ?_)
          exact Function.update_of_ne (Nat.ne_of_lt hx) _ _
        simp only [walk, hj, hw, Function.update_self, he]

/-- The undirected simple graph underlying a neighbour map. -/
def ofNbr (nbr : Fin n → Fin D → Fin n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => ∃ e, nbr u e = v)

/-- For an undirected neighbour map (every edge can be traversed backwards), reachability
along the neighbour map is exactly connectivity in the underlying simple graph. -/
theorem reach_iff_reachable [NeZero D] (nbr : Fin n → Fin D → Fin n)
    (hsym : ∀ (v : Fin n) (e : Fin D), ∃ e' : Fin D, nbr (nbr v e) e' = v) (s t : Fin n) :
    Reach nbr s t ↔ (ofNbr nbr).Reachable s t := by
  rw [reach_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b c _ hstep ih =>
        rcases eq_or_ne b c with rfl | hne
        · exact ih
        · exact ih.trans (SimpleGraph.Adj.reachable
            (show (ofNbr nbr).Adj b c from ⟨hne, Or.inl hstep⟩))
  · rintro ⟨w⟩
    induction w with
    | nil => exact Relation.ReflTransGen.refl
    | cons hadj _ ih =>
        refine Relation.ReflTransGen.head ?_ ih
        rcases hadj.2 with h | ⟨e, he⟩
        · exact h
        · obtain ⟨e', he'⟩ := hsym _ e
          exact ⟨e', by rw [he] at he'; exact he'⟩

/-! ## Branching programs

A *branching program* is the standard non-uniform model of space-bounded computation:
a program with `length` levels whose memory at each level is a state in the finite type
`S`.  At each level the program reads one position of the (read-only) input, chosen as a
function of the current state, and updates its state.  Its *size* is the number of nodes,
`length * card S`; a program of size `M` uses `log₂ M` bits of memory, so
*polynomial size = logarithmic space*. -/

structure BP (Q A S : Type) where
  /-- Number of levels of the program. -/
  length : ℕ
  /-- Initial state. -/
  start : S
  /-- Which input position is read at a given level and state. -/
  query : ℕ → S → Q
  /-- State transition, given the level, the state and the answer of the query. -/
  next : ℕ → S → A → S
  /-- Accepting states. -/
  accept : S → Bool

variable {Q A S : Type}

/-- The state of `P` on input `input` after `i` levels. -/
def BP.run (P : BP Q A S) (input : Q → A) : ℕ → S
  | 0 => P.start
  | i + 1 => P.next i (P.run input i) (input (P.query i (P.run input i)))

/-- The Boolean output of `P` on `input`. -/
def BP.eval (P : BP Q A S) (input : Q → A) : Bool := P.accept (P.run input P.length)

/-- The size (number of nodes) of a branching program. -/
def BP.size (P : BP Q A S) [Fintype S] : ℕ := P.length * Fintype.card S

/-! ## A small-space program for connectivity in graphs of small diameter -/

/-- The `j`-th digit of `i` in base `D`. -/
def dig (D : ℕ) [NeZero D] (i j : ℕ) : Fin D :=
  ⟨i / D ^ j % D, Nat.mod_lt _ (Nat.pos_of_neZero D)⟩

/-- The branching program that, on a `D`-regular graph on `Fin n`, tries out all `D ^ k`
direction sequences of length `k` starting at `s`, and accepts if it ever meets `t`.
Its memory consists of a single vertex together with one Boolean flag. -/
def ustconBP (n D k : ℕ) [NeZero D] (s t : Fin n) : BP (Fin n × Fin D) (Fin n) (Fin n × Bool) where
  length := D ^ k * k
  start := (s, decide (s = t))
  query := fun l p => (p.1, dig D (l / k) (l % k))
  next := fun l p a => (if (l + 1) % k = 0 then s else a, p.2 || decide (a = t))
  accept := fun p => p.2

private theorem div_mod_succ (hk : 0 < k) (l : ℕ) :
    (l + 1) % k = (l % k + 1) % k ∧ (l + 1) / k = (l % k + 1) / k + l / k := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < k ∧ l = k * q + r :=
    ⟨l / k, l % k, Nat.mod_lt _ hk, (Nat.div_add_mod l k).symm⟩
  have h1 : (k * q + r) % k = r := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have h2 : (k * q + r) / k = q := by
    rw [Nat.mul_add_div hk, Nat.div_eq_of_lt hr, Nat.add_zero]
  rw [h1, h2]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_assoc, Nat.mul_add_mod]
  · rw [Nat.add_assoc, Nat.mul_add_div hk, Nat.add_comm]

/-- The key invariant: after `l` levels the program is at the vertex reached by following
the `(l % k)` first directions of the `(l / k)`-th direction sequence, and its flag records
whether `t` has been met so far. -/
theorem ustconBP_run [NeZero D] (hk : 0 < k) (nbr : Fin n → Fin D → Fin n) (s t : Fin n)
    (l : ℕ) :
    ((ustconBP n D k s t).run (fun q => nbr q.1 q.2) l).1
        = walk nbr s (dig D (l / k)) (l % k)
      ∧ ((((ustconBP n D k s t).run (fun q => nbr q.1 q.2) l).2 = true)
        ↔ (s = t ∨ ∃ l' < l, walk nbr s (dig D (l' / k)) (l' % k + 1) = t)) := by
  induction l with
  | zero =>
      simp [BP.run, ustconBP, walk, Nat.zero_div, Nat.zero_mod]
  | succ l ih =>
      obtain ⟨ih1, ih2⟩ := ih
      obtain ⟨hm, hd⟩ := div_mod_succ (k := k) hk l
      have hstep : (ustconBP n D k s t).run (fun q => nbr q.1 q.2) (l + 1)
          = ((if (l + 1) % k = 0 then s else walk nbr s (dig D (l / k)) (l % k + 1)),
             ((ustconBP n D k s t).run (fun q => nbr q.1 q.2) l).2
                || decide (walk nbr s (dig D (l / k)) (l % k + 1) = t)) := by
        have e1 : (ustconBP n D k s t).run (fun q => nbr q.1 q.2) (l + 1)
            = (ustconBP n D k s t).next l ((ustconBP n D k s t).run (fun q => nbr q.1 q.2) l)
                (nbr (((ustconBP n D k s t).run (fun q => nbr q.1 q.2) l).1)
                  (dig D (l / k) (l % k))) := rfl
        rw [e1, ih1]
        rfl
      refine ⟨?_, ?_⟩
      · rw [hstep]
        by_cases h : (l + 1) % k = 0
        · rw [if_pos h, h]
          rfl
        · have hlt : l % k + 1 < k := by
            rcases Nat.lt_or_ge (l % k + 1) k with h' | h'
            · exact h'
            · exfalso
              have : l % k + 1 = k := le_antisymm (Nat.succ_le_of_lt (Nat.mod_lt _ hk)) h'
              rw [hm, this, Nat.mod_self] at h
              exact h rfl
          have h1 : (l + 1) % k = l % k + 1 := by
            rw [hm, Nat.mod_eq_of_lt hlt]
          have h2 : (l + 1) / k = l / k := by
            rw [hd, Nat.div_eq_of_lt hlt, Nat.zero_add]
          rw [h1, h2, if_neg (by omega)]
      · rw [hstep]
        simp only [Bool.or_eq_true, decide_eq_true_eq, ih2]
        constructor
        · rintro ((h | ⟨l', hl', hw⟩) | h)
          · exact Or.inl h
          · exact Or.inr ⟨l', by omega, hw⟩
          · exact Or.inr ⟨l, by omega, h⟩
        · rintro (h | ⟨l', hl', hw⟩)
          · exact Or.inl (Or.inl h)
          · rcases Nat.lt_or_ge l' l with h' | h'
            · exact Or.inl (Or.inr ⟨l', h', hw⟩)
            · have : l' = l := by omega
              subst this
              exact Or.inr hw

theorem dig_of_finFunctionFinEquiv [NeZero D] (w : ℕ → Fin D) (b : ℕ) (hb : b < k) :
    dig D ((finFunctionFinEquiv (fun i : Fin k => w i) : Fin (D ^ k)) : ℕ) b = w b := by
  have h : ((finFunctionFinEquiv (fun i : Fin k => w i) : Fin (D ^ k)) : ℕ)
      / D ^ (⟨b, hb⟩ : Fin k).1 % D = (w b : ℕ) :=
    congrArg Fin.val
      (congrFun (finFunctionFinEquiv.symm_apply_apply (fun i : Fin k => w i)) ⟨b, hb⟩)
  exact Fin.ext h

/-- **Correctness of the program.**  `ustconBP n D k s t` accepts the `D`-regular graph
`nbr` exactly when `t` can be reached from `s` by a walk of length at most `k`. -/
theorem ustconBP_eval [NeZero D] (hk : 0 < k) (nbr : Fin n → Fin D → Fin n) (s t : Fin n) :
    (ustconBP n D k s t).eval (fun q => nbr q.1 q.2) = true ↔ ReachWithin nbr s t k := by
  have h := ustconBP_run (n := n) (D := D) (k := k) hk nbr s t (D ^ k * k)
  have hlen : (ustconBP n D k s t).length = D ^ k * k := rfl
  rw [BP.eval, hlen]
  refine ⟨fun hacc => ?_, fun hreach => ?_⟩
  · have := h.2.1 hacc
    rcases this with hst | ⟨l, hl, hw⟩
    · exact ⟨fun _ => dig D 0 0, 0, Nat.zero_le _, hst⟩
    · exact ⟨dig D (l / k), l % k + 1, Nat.succ_le_of_lt (Nat.mod_lt _ hk), hw⟩
  · refine h.2.2 ?_
    obtain ⟨w, j, hj, hw⟩ := hreach
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact Or.inl hw
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      have hmk : m < k := by omega
      set i : ℕ := ((finFunctionFinEquiv (fun x : Fin k => w x) : Fin (D ^ k)) : ℕ) with hi
      have hik : i < D ^ k := (finFunctionFinEquiv (fun x : Fin k => w x)).isLt
      refine Or.inr ⟨k * i + m, ?_, ?_⟩
      · calc k * i + m < k * i + k := by omega
          _ = k * (i + 1) := by ring
          _ ≤ k * D ^ k := Nat.mul_le_mul_left _ hik
          _ = D ^ k * k := Nat.mul_comm _ _
      · have hdiv : (k * i + m) / k = i := by
          rw [Nat.mul_add_div hk, Nat.div_eq_of_lt hmk, Nat.add_zero]
        have hmod : (k * i + m) % k = m := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hmk]
        rw [hdiv, hmod]
        rw [← hw]
        refine walk_congr _ _ _ _ _ (fun x hx => ?_)
        exact dig_of_finFunctionFinEquiv (k := k) w x (by omega)

theorem ustconBP_size [NeZero D] (s t : Fin n) :
    (ustconBP n D k s t).size = D ^ k * k * (n * 2) := by
  simp [BP.size, ustconBP, Fintype.card_prod]

/-! ## The main statement -/

/--
**Reingold's theorem, scoped formalization.**

Reingold's theorem (`SL = L`) says that undirected `s`-`t` connectivity is decidable in
logarithmic space.  Its proof has two halves: a logspace graph transformation (based on the
zig-zag product) turning an arbitrary undirected graph into a constant-degree graph whose
connected components have logarithmic diameter, and then the observation that on such
graphs connectivity is decidable in logarithmic space by exhaustively enumerating all short
walks.  It is that second half which is formalized here, unconditionally, in the standard
non-uniform model of logarithmic space (branching programs of polynomial size, `size = 2 ^
space`).

Precisely: for all constants `c` and `d` there are constants `C`, `p` such that for every
`n` and all vertices `s t` of an `n`-vertex graph there is a branching program of size at
most `C * (n + 1) ^ p` (i.e. using `O(log n)` bits of memory) which reads the graph only
through its neighbour map, and which decides whether `s` and `t` are connected, for every
undirected `2 ^ d`-regular graph all of whose connected components have diameter at most
`c * (log₂ n + 1)`.

The hypothesis on `nbr` expresses that the graph is undirected: every edge can be traversed
backwards.  Connectivity is stated as `SimpleGraph.Reachable` in the underlying simple
graph `ofNbr nbr`, i.e. as ordinary undirected connectivity.
-/
theorem reingold_sl_l (c d : ℕ) :
    ∃ C p : ℕ, ∀ (n : ℕ) (s t : Fin n),
      ∃ P : BP (Fin n × Fin (2 ^ d)) (Fin n) (Fin n × Bool),
        P.size ≤ C * (n + 1) ^ p ∧
        ∀ nbr : Fin n → Fin (2 ^ d) → Fin n,
          (∀ (v : Fin n) (e : Fin (2 ^ d)), ∃ e' : Fin (2 ^ d), nbr (nbr v e) e' = v) →
          (∀ u v : Fin n, Reach nbr u v → ReachWithin nbr u v (c * (Nat.log 2 n + 1))) →
          (P.eval (fun q => nbr q.1 q.2) = true ↔ (ofNbr nbr).Reachable s t) := by
  refine ⟨2 ^ (d + d * c) * 2 * (c + 1), d * c + 2, ?_⟩
  intro n s t
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = c * (Nat.log 2 n + 1) + 1 := ⟨_, rfl⟩
  have hkpos : 0 < k := by omega
  refine ⟨ustconBP n (2 ^ d) k s t, ?_, ?_⟩
  · -- the program has polynomial size, i.e. it uses `O(log n)` bits of memory
    rw [ustconBP_size]
    have h2L : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    have hpow : (2 ^ d) ^ k ≤ 2 ^ d * (2 ^ (d * c) * (n + 1) ^ (d * c)) := by
      have hrw : (2 ^ d) ^ k = 2 ^ d * (2 ^ (Nat.log 2 n + 1)) ^ (d * c) := by
        rw [hk, ← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        ring
      rw [hrw]
      refine Nat.mul_le_mul_left _ ?_
      rw [← Nat.mul_pow]
      refine Nat.pow_le_pow_left ?_ _
      calc 2 ^ (Nat.log 2 n + 1) = 2 * 2 ^ Nat.log 2 n := by ring
        _ ≤ 2 * n := Nat.mul_le_mul_left _ h2L
        _ ≤ 2 * (n + 1) := by omega
    have hkle : k ≤ (c + 1) * (n + 1) := by
      have hLn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
      have h3 : c * (Nat.log 2 n + 1) ≤ c * (n + 1) := Nat.mul_le_mul_left c (by omega)
      have h4 : (c + 1) * (n + 1) = c * (n + 1) + (n + 1) := by ring
      linarith
    calc (2 ^ d) ^ k * k * (n * 2)
        ≤ (2 ^ d * (2 ^ (d * c) * (n + 1) ^ (d * c))) * ((c + 1) * (n + 1)) * (2 * (n + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul hpow hkle) (by omega)
      _ = 2 ^ (d + d * c) * 2 * (c + 1) * (n + 1) ^ (d * c + 2) := by
          rw [pow_add 2 d (d * c), pow_add (n + 1) (d * c) 2]
          ring
  · -- the program decides connectivity
    intro nbr hsym hdiam
    rw [ustconBP_eval hkpos, ← reach_iff_reachable nbr hsym]
    exact ⟨fun h => h.reach, fun h => (hdiam s t h).mono (by omega)⟩

/-- The hypotheses of `CS.reingold_sl_l` are satisfiable: the complete graph with self-loops
on `2 ^ d` vertices is an undirected `2 ^ d`-regular graph of diameter `1`, in which every
pair of vertices is connected.  (So the main theorem is not vacuous.) -/
theorem reingold_hypotheses_satisfiable (c d : ℕ) (hc : 0 < c) :
    ∃ nbr : Fin (2 ^ d) → Fin (2 ^ d) → Fin (2 ^ d),
      (∀ (v : Fin (2 ^ d)) (e : Fin (2 ^ d)), ∃ e' : Fin (2 ^ d), nbr (nbr v e) e' = v) ∧
      (∀ u v : Fin (2 ^ d), Reach nbr u v →
        ReachWithin nbr u v (c * (Nat.log 2 (2 ^ d) + 1))) ∧
      (∀ u v : Fin (2 ^ d), Reach nbr u v) := by
  refine ⟨fun _ e => e, fun v _ => ⟨v, rfl⟩, fun u v _ => ⟨fun _ => v, 1, ?_, rfl⟩,
    fun u v => ⟨fun _ => v, 1, rfl⟩⟩
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (Nat.succ_ne_zero _))

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

