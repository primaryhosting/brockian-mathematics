import Mathlib

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-! ## A model of bounded-memory (space-bounded) computation

A `Alg Q Ans In Out` is a deterministic algorithm which

* has a finite set `S` of memory configurations,
* starts, on input `x : In`, in configuration `init x`,
* in each configuration either *halts* with an output in `Out`, or issues a query `q : Q`
  about its (read-only) input and moves to a new configuration determined by the answer.

The *space* used by the algorithm is `Nat.log 2 (card A)`, so "logarithmic space" means
`A.card ≤ p n` for a polynomial `p`.  This is the standard configuration-counting
characterisation of deterministic logarithmic space: a machine with a read-only input and
`c * log n` bits of work memory has polynomially many configurations, and conversely.
-/

structure Alg (Q Ans In Out : Type) where
  /-- The finite set of memory configurations. -/
  S : Type
  /-- Finiteness of the configuration space. -/
  fin : Fintype S
  /-- Initial configuration on a given input. -/
  init : In → S
  /-- In each configuration, either query the input and continue, or halt with an output. -/
  trans : S → ((Q × (Ans → S)) ⊕ Out)

namespace Alg

variable {Q Ans In Out : Type}

/-- The number of memory configurations; `Nat.log 2` of it is the space used. -/
def card (A : Alg Q Ans In Out) : ℕ := @Fintype.card A.S A.fin

/-- The output of a configuration, `none` if the algorithm has not halted. -/
def out (A : Alg Q Ans In Out) (σ : A.S) : Option Out :=
  match A.trans σ with
  | Sum.inl _ => none
  | Sum.inr y => some y

/-- One step of the computation, relative to an oracle `o` answering queries. -/
def stepOnce (A : Alg Q Ans In Out) (o : Q → Ans) (σ : A.S) : A.S :=
  match A.trans σ with
  | Sum.inl (q, f) => f (o q)
  | Sum.inr _ => σ

/-- Iterating the computation. -/
def iter (A : Alg Q Ans In Out) (o : Q → Ans) : ℕ → A.S → A.S
  | 0, σ => σ
  | k + 1, σ => A.stepOnce o (A.iter o k σ)

/-- `A` on input `x` (with oracle `o`) eventually halts with output `y`. -/
def Outputs (A : Alg Q Ans In Out) (o : Q → Ans) (x : In) (y : Out) : Prop :=
  ∃ k, A.out (A.iter o k (A.init x)) = some y

lemma stepOnce_of_halted {A : Alg Q Ans In Out} {o : Q → Ans} {σ : A.S} {y : Out}
    (h : A.out σ = some y) : A.stepOnce o σ = σ := by
  unfold out at h
  unfold stepOnce
  cases hh : A.trans σ with
  | inl p => rw [hh] at h; simp at h
  | inr y' => rfl

lemma iter_of_halted {A : Alg Q Ans In Out} {o : Q → Ans} {σ : A.S} {y : Out}
    (h : A.out σ = some y) : ∀ k, A.iter o k σ = σ := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [iter, ih, stepOnce_of_halted h]

lemma iter_add (A : Alg Q Ans In Out) (o : Q → Ans) (k₁ k₂ : ℕ) (σ : A.S) :
    A.iter o (k₁ + k₂) σ = A.iter o k₂ (A.iter o k₁ σ) := by
  induction k₂ with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, iter, iter, ih]

/-- Determinism: an algorithm has at most one output on a given input. -/
lemma Outputs_unique {A : Alg Q Ans In Out} {o : Q → Ans} {x : In} {y y' : Out}
    (h : A.Outputs o x y) (h' : A.Outputs o x y') : y = y' := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk'⟩ := h'
  rcases le_total k k' with hle | hle
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [iter_add, iter_of_halted hk] at hk'
    rw [hk] at hk'; exact Option.some.inj hk'
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [iter_add, iter_of_halted hk'] at hk
    rw [hk'] at hk; exact (Option.some.inj hk).symm

end Alg

/-! ## Walks in a bounded-degree graph given by a neighbour map -/

/-- Following a sequence of edge labels from a vertex. -/
def walk {N d : ℕ} (nbr : Fin N → Fin d → Fin N) : Fin N → List (Fin d) → Fin N
  | v, [] => v
  | v, a :: l => walk nbr (nbr v a) l

/-- Reachability along labelled walks. -/
def WalkReach {N d : ℕ} (nbr : Fin N → Fin d → Fin N) (v w : Fin N) : Prop :=
  ∃ l : List (Fin d), walk nbr v l = w

/-- The `j`-th base-`d` digit of `k`, as an element of `Fin d`. -/
def digit (d k j : ℕ) (hd : 0 < d) : Fin d := ⟨(k / d ^ j) % d, Nat.mod_lt _ hd⟩

/-- The vertex reached after `j` steps of the walk from `v` whose labels are the
base-`d` digits of `k`. -/
def posP {N d : ℕ} (nbr : Fin N → Fin d → Fin N) (hd : 0 < d) : Fin N → ℕ → ℕ → Fin N
  | v, _, 0 => v
  | v, k, (j + 1) => posP nbr hd (nbr v (digit d k 0 hd)) (k / d) j

lemma digit_div (d k j : ℕ) (hd : 0 < d) : digit d (k / d) j hd = digit d k (j + 1) hd := by
  unfold digit
  have : k / d / d ^ j = k / d ^ (j + 1) := by
    rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
  simp [this]

lemma posP_succ {N d : ℕ} (nbr : Fin N → Fin d → Fin N) (hd : 0 < d) :
    ∀ (j : ℕ) (v : Fin N) (k : ℕ),
      posP nbr hd v k (j + 1) = nbr (posP nbr hd v k j) (digit d k j hd) := by
  intro j
  induction j with
  | zero => intro v k; rfl
  | succ j ih =>
      intro v k
      show posP nbr hd (nbr v (digit d k 0 hd)) (k / d) (j + 1) = _
      rw [ih]
      rw [digit_div]
      rfl

/-- Every `posP` vertex is reachable by a walk of the corresponding length. -/
lemma posP_walk {N d : ℕ} (nbr : Fin N → Fin d → Fin N) (hd : 0 < d) :
    ∀ (j : ℕ) (v : Fin N) (k : ℕ), ∃ l : List (Fin d), l.length = j ∧
      walk nbr v l = posP nbr hd v k j := by
  intro j
  induction j with
  | zero => intro v k; exact ⟨[], rfl, rfl⟩
  | succ j ih =>
      intro v k
      obtain ⟨l, hl, hw⟩ := ih (nbr v (digit d k 0 hd)) (k / d)
      exact ⟨digit d k 0 hd :: l, by simp [hl], by simpa [walk] using hw⟩

/-- Base-`d` encoding of a list of digits (least significant first). -/
def enc (d : ℕ) : List (Fin d) → ℕ
  | [] => 0
  | a :: l => (a : ℕ) + d * enc d l

lemma enc_lt {d : ℕ} (hd : 0 < d) : ∀ l : List (Fin d), enc d l < d ^ l.length := by
  intro l
  induction l with
  | nil => simpa [enc] using hd
  | cons a l ih =>
      have h1 : enc d l + 1 ≤ d ^ l.length := ih
      have h2 : (a : ℕ) + d * enc d l < d * (enc d l + 1) := by
        have := a.isLt
        nlinarith [a.isLt]
      calc (a : ℕ) + d * enc d l < d * (enc d l + 1) := h2
        _ ≤ d * d ^ l.length := Nat.mul_le_mul_left _ h1
        _ = d ^ (l.length + 1) := by ring
      
/-- The walk determined by the digits of `enc d l` is exactly the walk with labels `l`. -/
lemma posP_enc {N d : ℕ} (nbr : Fin N → Fin d → Fin N) (hd : 0 < d) :
    ∀ (l : List (Fin d)) (v : Fin N), posP nbr hd v (enc d l) l.length = walk nbr v l := by
  intro l
  induction l with
  | nil => intro v; rfl
  | cons a l ih =>
      intro v
      have hmod : digit d (enc d (a :: l)) 0 hd = a := by
        apply Fin.ext
        simp [digit, enc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
      have hdiv : enc d (a :: l) / d = enc d l := by
        simp [enc, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt a.isLt]
      show posP nbr hd (nbr v (digit d (enc d (a :: l)) 0 hd)) (enc d (a :: l) / d) l.length = _
      rw [hmod, hdiv, ih]
      rfl

/-! ## The exhaustive-walk algorithm

For a graph of degree `d` all of whose components have diameter at most `D`, `s`-`t`
connectivity is decided by trying, one after the other, all `d ^ D` label sequences of
length `D`, and checking whether `t` occurs on the corresponding walk from `s`.

The memory used is a label sequence (`D * log d` bits), a step counter, and three vertex
names, hence `O(D * log d + log N)` bits.  For `d` constant and `D = O(log N)` this is
logarithmic space -- this is the final step of Reingold's algorithm.
-/

/-- Configurations of the exhaustive-walk algorithm: either a running configuration
`(s, t, k, j, v)` (source, target, current label sequence, step counter, current vertex),
or a halted configuration carrying the answer. -/
abbrev ES (N d D : ℕ) : Type :=
  (Fin N × Fin N × Fin (d ^ D) × Fin (D + 1) × Fin N) ⊕ Bool

/-- The transition function of the exhaustive-walk algorithm. -/
def etrans (N d D : ℕ) (hd : 0 < d) :
    ES N d D → (((Fin N × Fin d) × (Fin N → ES N d D)) ⊕ Bool)
  | Sum.inr b => Sum.inr b
  | Sum.inl (s, t, k, j, v) =>
      if v = t then Sum.inr true
      else if hj : (j : ℕ) < D then
        Sum.inl ((v, digit d (k : ℕ) (j : ℕ) hd),
          fun u => Sum.inl (s, t, k, ⟨(j : ℕ) + 1, by omega⟩, u))
      else if hk : (k : ℕ) + 1 < d ^ D then
        Sum.inl ((v, digit d (k : ℕ) (j : ℕ) hd),
          fun _ => Sum.inl (s, t, ⟨(k : ℕ) + 1, hk⟩, ⟨0, Nat.succ_pos D⟩, s))
      else Sum.inr false

/-- The exhaustive-walk algorithm. -/
def enumAlg (N d D : ℕ) (hd : 0 < d) :
    Alg (Fin N × Fin d) (Fin N) (Fin N × Fin N) Bool where
  S := ES N d D
  fin := inferInstance
  init := fun p =>
    Sum.inl (p.1, p.2, ⟨0, Nat.pos_pow_of_pos _ hd⟩, ⟨0, Nat.succ_pos D⟩, p.1)
  trans := etrans N d D hd

lemma enumAlg_card (N d D : ℕ) (hd : 0 < d) :
    (enumAlg N d D hd).card = N * N * d ^ D * (D + 1) * N + 2 := by
  simp [Alg.card, enumAlg, ES]
  ring

section Correct

variable {N d D : ℕ} (hd : 0 < d) (nbr : Fin N → Fin d → Fin N) (s t : Fin N)

/-- The oracle: answer the query `(v, i)` with the `i`-th neighbour of `v`. -/
def nbrOracle (nbr : Fin N → Fin d → Fin N) : Fin N × Fin d → Fin N := fun p => nbr p.1 p.2

/-- The configuration after `n` steps. -/
def erun (n : ℕ) : ES N d D :=
  (enumAlg N d D hd).iter (nbrOracle nbr) n ((enumAlg N d D hd).init (s, t))

lemma erun_zero : erun hd nbr s t 0 = Sum.inl (s, t, ⟨0, Nat.pos_pow_of_pos _ hd⟩,
    ⟨0, Nat.succ_pos D⟩, s) := rfl

lemma erun_succ (n : ℕ) :
    erun hd nbr s t (n + 1) =
      (enumAlg N d D hd).stepOnce (nbrOracle nbr) (erun hd nbr s t n) := rfl

/-- The invariant maintained along the run. -/
def Good : ES N d D → Prop
  | Sum.inl (s', t', k, j, v) => s' = s ∧ t' = t ∧ v = posP nbr hd s (k : ℕ) (j : ℕ)
  | Sum.inr b => b = true → WalkReach nbr s t

lemma good_step (σ : ES N d D) (h : Good hd nbr s t σ) :
    Good hd nbr s t ((enumAlg N d D hd).stepOnce (nbrOracle nbr) σ) := by
  match σ with
  | Sum.inr b => simpa [Alg.stepOnce, enumAlg, etrans] using h
  | Sum.inl (s', t', k, j, v) =>
      obtain ⟨rfl, rfl, hv⟩ := h
      by_cases hvt : v = t
      · have : (enumAlg N d D hd).stepOnce (nbrOracle nbr) (Sum.inl (s, t, k, j, v))
            = Sum.inr true := by
          simp [Alg.stepOnce, enumAlg, etrans, hvt]
        rw [this]
        intro _
        obtain ⟨l, _, hl⟩ := posP_walk nbr hd (j : ℕ) s (k : ℕ)
        exact ⟨l, by rw [hl, ← hv, hvt]⟩
      · by_cases hj : (j : ℕ) < D
        · have : (enumAlg N d D hd).stepOnce (nbrOracle nbr) (Sum.inl (s, t, k, j, v))
              = Sum.inl (s, t, k, ⟨(j : ℕ) + 1, by omega⟩,
                  nbr v (digit d (k : ℕ) (j : ℕ) hd)) := by
            simp [Alg.stepOnce, enumAlg, etrans, hvt, hj, nbrOracle]
          rw [this]
          refine ⟨rfl, rfl, ?_⟩
          rw [hv, ← posP_succ]
        · by_cases hk : (k : ℕ) + 1 < d ^ D
          · have : (enumAlg N d D hd).stepOnce (nbrOracle nbr) (Sum.inl (s, t, k, j, v))
                = Sum.inl (s, t, ⟨(k : ℕ) + 1, hk⟩, ⟨0, Nat.succ_pos D⟩, s) := by
              simp [Alg.stepOnce, enumAlg, etrans, hvt, hj, hk, nbrOracle]
            rw [this]
            exact ⟨rfl, rfl, rfl⟩
          · have : (enumAlg N d D hd).stepOnce (nbrOracle nbr) (Sum.inl (s, t, k, j, v))
                = Sum.inr false := by
              simp [Alg.stepOnce, enumAlg, etrans, hvt, hj, hk]
            rw [this]
            simp

lemma good_erun (n : ℕ) : Good hd nbr s t (erun hd nbr s t n) := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih => rw [erun_succ]; exact good_step hd nbr s t _ ih

/-- If the algorithm ever answers `true`, then `t` is reachable from `s`. -/
lemma sound_true (n : ℕ) (h : (enumAlg N d D hd).out (erun hd nbr s t n) = some true) :
    WalkReach nbr s t := by
  have hg := good_erun hd nbr s t n
  match hσ : erun hd nbr s t n with
  | Sum.inr b =>
      rw [hσ] at h
      have hb : b = true := by
        simpa [Alg.out, enumAlg, etrans] using h
      rw [hσ] at hg
      exact hg hb
  | Sum.inl (s', t', k, j, v) =>
      rw [hσ] at h
      simp only [Alg.out, enumAlg, etrans] at h
      by_cases hvt : v = t'
      · simp [hvt] at h
        -- halted with `true`; extract reachability from the invariant
        rw [hσ] at hg
        obtain ⟨rfl, rfl, hv⟩ := hg
        obtain ⟨l, _, hl⟩ := posP_walk nbr hd (j : ℕ) s (k : ℕ)
        exact ⟨l, by rw [hl, ← hv, hvt]⟩
      · by_cases hj : (j : ℕ) < D
        · simp [hvt, hj] at h
        · by_cases hk : (k : ℕ) + 1 < d ^ D
          · simp [hvt, hj, hk] at h
          · simp [hvt, hj, hk] at h

/-- Inner loop: from the start of the `k`-th label sequence we reach every step `j ≤ D`
of that sequence, unless the algorithm has already answered `true`. -/
lemma run_inner (k : Fin (d ^ D))
    (h0 : ∃ n, erun hd nbr s t n = Sum.inl (s, t, k, ⟨0, Nat.succ_pos D⟩, s)) :
    ∀ j : ℕ, ∀ hj : j ≤ D,
      (∃ n, erun hd nbr s t n =
          Sum.inl (s, t, k, ⟨j, Nat.lt_succ_of_le hj⟩, posP nbr hd s (k : ℕ) j)) ∨
      (∃ n, (enumAlg N d D hd).out (erun hd nbr s t n) = some true) := by
  intro j
  induction j with
  | zero => intro _; exact Or.inl h0
  | succ j ih =>
      intro hj
      have hj' : j ≤ D := by omega
      rcases ih hj' with ⟨n, hn⟩ | h
      · set v := posP nbr hd s (k : ℕ) j with hvdef
        by_cases hvt : v = t
        · refine Or.inr ⟨n + 1, ?_⟩
          have hstep : erun hd nbr s t (n + 1) = Sum.inr true := by
            rw [erun_succ, hn]
            simp [Alg.stepOnce, enumAlg, etrans, hvt]
          rw [hstep]
          simp [Alg.out, enumAlg, etrans]
        · have hjD : j < D := by omega
          refine Or.inl ⟨n + 1, ?_⟩
          rw [erun_succ, hn]
          have : (enumAlg N d D hd).stepOnce (nbrOracle nbr)
              (Sum.inl (s, t, k, (⟨j, Nat.lt_succ_of_le hj'⟩ : Fin (D + 1)), v))
              = Sum.inl (s, t, k, ⟨j + 1, by omega⟩,
                  nbr v (digit d (k : ℕ) j hd)) := by
            simp [Alg.stepOnce, enumAlg, etrans, hvt, hjD, nbrOracle]
          rw [this, hvdef, ← posP_succ]
      · exact Or.inr h

/-- Outer loop: the algorithm starts every label sequence, unless it answers `true` first. -/
lemma run_outer :
    ∀ k : ℕ, ∀ hk : k < d ^ D,
      (∃ n, erun hd nbr s t n = Sum.inl (s, t, ⟨k, hk⟩, ⟨0, Nat.succ_pos D⟩, s)) ∨
      (∃ n, (enumAlg N d D hd).out (erun hd nbr s t n) = some true) := by
  intro k
  induction k with
  | zero => intro hk; exact Or.inl ⟨0, rfl⟩
  | succ k ih =>
      intro hk
      have hk' : k < d ^ D := by omega
      rcases ih hk' with h0 | h
      · rcases run_inner hd nbr s t ⟨k, hk'⟩ h0 D le_rfl with ⟨n, hn⟩ | h
        · set v := posP nbr hd s k D with hvdef
          by_cases hvt : v = t
          · refine Or.inr ⟨n + 1, ?_⟩
            have hstep : erun hd nbr s t (n + 1) = Sum.inr true := by
              rw [erun_succ, hn]
              simp [Alg.stepOnce, enumAlg, etrans, hvt]
            rw [hstep]; simp [Alg.out, enumAlg, etrans]
          · refine Or.inl ⟨n + 1, ?_⟩
            rw [erun_succ, hn]
            simp [Alg.stepOnce, enumAlg, etrans, hvt, hk, nbrOracle]
        · exact Or.inr h
      · exact Or.inr h

end Correct

/-- **The exhaustive-walk algorithm is correct.**  If every pair of vertices joined by a
walk is joined by a walk of length at most `D`, then `enumAlg` decides reachability. -/
theorem enumAlg_decides (N d D : ℕ) (hd : 0 < d) (nbr : Fin N → Fin d → Fin N)
    (hdiam : ∀ v w : Fin N, WalkReach nbr v w → ∃ l : List (Fin d),
      l.length ≤ D ∧ walk nbr v l = w) (s t : Fin N) :
    ∃ b : Bool, (enumAlg N d D hd).Outputs (nbrOracle nbr) (s, t) b ∧
      (b = true ↔ WalkReach nbr s t) := by
  by_cases hreach : WalkReach nbr s t
  · refine ⟨true, ?_, by simp [hreach]⟩
    obtain ⟨l, hlen, hl⟩ := hdiam s t hreach
    have hk : enc d l < d ^ D :=
      lt_of_lt_of_le (enc_lt hd l) (Nat.pow_le_pow_right hd hlen)
    rcases run_outer hd nbr s t (enc d l) hk with h0 | h
    · rcases run_inner hd nbr s t ⟨enc d l, hk⟩ h0 l.length (by omega) with ⟨n, hn⟩ | h
      · refine ⟨n + 1, ?_⟩
        have hv : posP nbr hd s (enc d l) l.length = t := by
          rw [posP_enc nbr hd l s, hl]
        have hstep : erun hd nbr s t (n + 1) = Sum.inr true := by
          rw [erun_succ, hn]
          simp [Alg.stepOnce, enumAlg, etrans, hv]
        show (enumAlg N d D hd).out (erun hd nbr s t (n + 1)) = some true
        rw [hstep]; simp [Alg.out, enumAlg, etrans]
      · exact h
    · exact h
  · refine ⟨false, ?_, by simp [hreach]⟩
    have hne : ∀ (k j : ℕ), posP nbr hd s k j ≠ t := by
      intro k j hcontra
      obtain ⟨l, _, hl⟩ := posP_walk nbr hd j s k
      exact hreach ⟨l, by rw [hl, hcontra]⟩
    have hd0 : 0 < d ^ D := Nat.pos_pow_of_pos _ hd
    rcases run_outer hd nbr s t (d ^ D - 1) (by omega) with h0 | h
    · rcases run_inner hd nbr s t ⟨d ^ D - 1, by omega⟩ h0 D le_rfl with ⟨n, hn⟩ | h
      · refine ⟨n + 1, ?_⟩
        have hvt : posP nbr hd s (d ^ D - 1) D ≠ t := hne _ _
        have hk : ¬ ((d ^ D - 1) + 1 < d ^ D) := by omega
        have hstep : erun hd nbr s t (n + 1) = Sum.inr false := by
          rw [erun_succ, hn]
          simp [Alg.stepOnce, enumAlg, etrans, hvt, hk]
        show (enumAlg N d D hd).out (erun hd nbr s t (n + 1)) = some false
        rw [hstep]; simp [Alg.out, enumAlg, etrans]
      · exact absurd (sound_true hd nbr s t h.choose h.choose_spec) hreach
    · exact absurd (sound_true hd nbr s t h.choose h.choose_spec) hreach

/-! ## Undirected `s`-`t` connectivity and the class L -/

/-- Undirected reachability in a graph given by a symmetric Boolean adjacency matrix. -/
def AdjReach {n : ℕ} (adj : Fin n → Fin n → Bool) : Fin n → Fin n → Prop :=
  Relation.ReflTransGen (fun u v => adj u v = true)

/-- Algorithms for `USTCON` on `n`-vertex graphs: the input is the adjacency matrix,
queried bit by bit, together with the two vertices `s`, `t`. -/
abbrev UAlg (n : ℕ) : Type := Alg (Fin n × Fin n) Bool (Fin n × Fin n) Bool

/-- The adjacency-matrix oracle. -/
def adjOracle {n : ℕ} (adj : Fin n → Fin n → Bool) : Fin n × Fin n → Bool :=
  fun p => adj p.1 p.2

/-- `A` decides undirected `s`-`t` connectivity on `n`-vertex graphs. -/
def DecidesUSTCON (n : ℕ) (A : UAlg n) : Prop :=
  ∀ adj : Fin n → Fin n → Bool, (∀ u v, adj u v = adj v u) → ∀ s t : Fin n,
    ∃ b : Bool, A.Outputs (adjOracle adj) (s, t) b ∧ (b = true ↔ AdjReach adj s t)

/-- **`USTCON ∈ L`**: undirected `s`-`t` connectivity is decided by a family of algorithms
using only polynomially many memory configurations, i.e. logarithmically many bits of
work memory. -/
def USTCONinL : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, ∃ A : UAlg n, A.card ≤ (n + 2) ^ c ∧ DecidesUSTCON n A

/-! ## Reingold's expanderisation step

Reingold's theorem is obtained by combining the (fully proved) exhaustive-walk algorithm
above with the expanderisation step: every undirected graph can be turned, in logarithmic
space, into a `4`-regular graph on polynomially many vertices with the same connectivity
structure and with all connected components of logarithmic diameter.  The following
structure packages exactly that step, together with the standard fact that a logarithmic
space subroutine can be composed with a logarithmic-space computation at the cost of a
polynomial blow-up in the number of configurations. -/

structure ReingoldTransform where
  /-- Exponent of the polynomial bounds. -/
  c : ℕ
  /-- Number of vertices of the transformed graph. -/
  N : ℕ → ℕ
  /-- Diameter bound of the transformed graph. -/
  D : ℕ → ℕ
  /-- Embedding of the original vertices into the transformed graph. -/
  emb : (n : ℕ) → Fin n → Fin (N n)
  /-- The neighbour (rotation) map of the transformed graph. -/
  nbr : (n : ℕ) → (Fin n → Fin n → Bool) → Fin (N n) → Fin 4 → Fin (N n)
  /-- The transformed graph has polynomially many vertices. -/
  hN : ∀ n, N n ≤ (n + 2) ^ c
  /-- The diameter is logarithmic: `4 ^ D n * (D n + 1)` is polynomial. -/
  hD : ∀ n, 4 ^ D n * (D n + 1) ≤ (n + 2) ^ c
  /-- Every connected component of the transformed graph has diameter at most `D n`. -/
  diam : ∀ (n : ℕ) (adj : Fin n → Fin n → Bool), (∀ u v, adj u v = adj v u) →
    ∀ v w : Fin (N n), WalkReach (nbr n adj) v w →
      ∃ l : List (Fin 4), l.length ≤ D n ∧ walk (nbr n adj) v l = w
  /-- The transformation preserves connectivity. -/
  preserve : ∀ (n : ℕ) (adj : Fin n → Fin n → Bool), (∀ u v, adj u v = adj v u) →
    ∀ s t : Fin n, AdjReach adj s t ↔ WalkReach (nbr n adj) (emb n s) (emb n t)
  /-- The neighbour map of the transformed graph is computable in logarithmic space:
  any algorithm which queries it can be simulated by an algorithm which queries the
  adjacency matrix of the original graph, with a polynomial blow-up in memory. -/
  simulate : ∀ (n : ℕ)
      (B : Alg (Fin (N n) × Fin 4) (Fin (N n)) (Fin (N n) × Fin (N n)) Bool),
    ∃ A : UAlg n, A.card ≤ B.card * (n + 2) ^ c ∧
      ∀ (adj : Fin n → Fin n → Bool), (∀ u v, adj u v = adj v u) → ∀ (s t : Fin n) (b : Bool),
        B.Outputs (nbrOracle (nbr n adj)) (emb n s, emb n t) b →
          A.Outputs (adjOracle adj) (s, t) b

/-- **Reingold's theorem (`SL = L`): undirected `s`-`t` connectivity is in `L`.**

Given the expanderisation step `T` (Reingold's zig-zag / derandomised-squaring
construction, which turns any undirected graph into a connectivity-equivalent
`4`-regular graph of logarithmic diameter in logarithmic space), undirected `s`-`t`
connectivity is decided in logarithmic space: the exhaustive-walk algorithm on the
transformed graph uses only `O(log n)` bits, and simulating it over the original graph
costs only a polynomial factor in the number of configurations. -/
theorem reingold_sl_l (T : ReingoldTransform) : USTCONinL := by
  refine ⟨5 * T.c + 2, ?_⟩
  intro n
  set c := T.c with hc
  set B := enumAlg (T.N n) 4 (T.D n) (by norm_num) with hB
  obtain ⟨A, hcard, hsim⟩ := T.simulate n B
  refine ⟨A, ?_, ?_⟩
  · -- the memory bound
    have hBcard : B.card = T.N n * T.N n * 4 ^ T.D n * (T.D n + 1) * T.N n + 2 := by
      rw [hB, enumAlg_card]
    have hNn : T.N n ≤ (n + 2) ^ c := T.hN n
    have hDn : 4 ^ T.D n * (T.D n + 1) ≤ (n + 2) ^ c := T.hD n
    have hpos : 1 ≤ (n + 2) ^ c := Nat.one_le_pow _ _ (by omega)
    have key : B.card ≤ (n + 2) ^ (4 * c + 2) := by
      have h1 : T.N n * T.N n * 4 ^ T.D n * (T.D n + 1) * T.N n
          ≤ (n + 2) ^ c * (n + 2) ^ c * (n + 2) ^ c * (n + 2) ^ c := by
        calc T.N n * T.N n * 4 ^ T.D n * (T.D n + 1) * T.N n
            = (T.N n * T.N n * T.N n) * (4 ^ T.D n * (T.D n + 1)) := by ring
          _ ≤ ((n + 2) ^ c * (n + 2) ^ c * (n + 2) ^ c) * ((n + 2) ^ c) := by
              exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hNn hNn) hNn) hDn
          _ = (n + 2) ^ c * (n + 2) ^ c * (n + 2) ^ c * (n + 2) ^ c := by ring
      have h2 : (n + 2) ^ c * (n + 2) ^ c * (n + 2) ^ c * (n + 2) ^ c + 2
          ≤ (n + 2) ^ (4 * c + 2) := by
        have hexp : (n + 2) ^ (4 * c + 2) = ((n + 2) ^ c * (n + 2) ^ c *
            ((n + 2) ^ c * (n + 2) ^ c)) * ((n + 2) * (n + 2)) := by
          rw [show 4 * c + 2 = c + c + c + c + 1 + 1 by ring]
          ring
        rw [hexp]
        have h4 : 4 ≤ (n + 2) * (n + 2) := by nlinarith
        have hprod : 1 ≤ (n + 2) ^ c * (n + 2) ^ c * ((n + 2) ^ c * (n + 2) ^ c) := by
          exact Nat.one_le_iff_ne_zero.mpr (by positivity)
        nlinarith [hprod, h4]
      omega
    calc A.card ≤ B.card * (n + 2) ^ c := hcard
      _ ≤ (n + 2) ^ (4 * c + 2) * (n + 2) ^ c := Nat.mul_le_mul_right _ key
      _ = (n + 2) ^ (5 * c + 2) := by rw [← pow_add]; ring_nf
  · -- correctness
    intro adj hsymm s t
    obtain ⟨b, hout, hb⟩ :=
      enumAlg_decides (T.N n) 4 (T.D n) (by norm_num) (T.nbr n adj)
        (T.diam n adj hsymm) (T.emb n s) (T.emb n t)
    exact ⟨b, hsim adj hsymm s t b hout, by rw [hb, ← T.preserve n adj hsymm]⟩

end CS

