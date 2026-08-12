/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Reingold.Machine

/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalised here

Undirected `s`-`t` connectivity (`USTCON`) is decided in logarithmic space.

The machine model is the one of `CS.Solver`: a deterministic machine whose whole memory
is one configuration out of a finite configuration space `State`, which reads the
adjacency matrix of the `n`-vertex input graph one bit at a time (in each configuration
it queries one entry and branches on the answer) and which is started in a
configuration determined by the two distinguished vertices.  Using `O(log n)` bits of
memory means `Fintype.card State ≤ c * n ^ c` for a constant `c` that does not depend
on `n`.

`CS.reingold_sl_l` states, and proves, that USTCON is solved by such machines: there is
a single constant `c` (here `c = 100`) such that for every `n` there is a machine with
at most `c * n ^ c` configurations deciding connectivity on all `n`-vertex undirected
graphs.  The machine is built from a universal traversal sequence of length `O(n⁷)`,
whose existence is proved from scratch in `CS.exists_uts`: the transition operator of
the lazy `2n`-regular walk attached to a graph is shown to be symmetric and positive
semidefinite, to have spectral gap at least `1/(4n³)` on each connected component
(`CS.gap`), hence to reach any prescribed vertex of the component with probability at
least `1/(2n)` after `8n⁴` steps (`CS.hit_prob`), and a union bound over all graphs and
all pairs of vertices produces a single label sequence that works for all of them.

*Scope.*  The machine family produced here is described by a single constant `c` and one
machine per input size; the construction of the traversal sequence is by the
probabilistic method, so the family is not exhibited as a *uniformly computable* one.
Reingold's theorem `SL = L` is the strengthening in which the machine family is
uniformly computable; that statement is spelled out below as `CS.SLeqL` and is *not*
proved in this file.
-/

namespace CS

/-- **Undirected `s`-`t` connectivity in logarithmic space.**

There is a constant `c` such that, for every number of vertices `n ≥ 1`, undirected
`s`-`t` connectivity on `n`-vertex graphs is decided by a machine which reads the
adjacency matrix one bit at a time and whose configuration space has at most `c * n ^ c`
elements, i.e. which uses `O(log n)` bits of memory.

See the module documentation for the precise scope of this statement: the uniform
(`SL = L`) form of the theorem is stated as `CS.SLeqL` below and is not proved here. -/
theorem reingold_sl_l :
    ∃ c : ℕ, ∀ n : ℕ, 0 < n → ∃ M : Solver n,
      Fintype.card M.State ≤ c * n ^ c ∧ M.Correct :=
  ustcon_logspace

/-! ### The uniform statement -/

/-- The machine on `n` vertices described by numerical data: configurations are the
numbers `0, …, w n`, and `init`, `qry`, `nxt`, `outp` describe the initial
configuration, the queried adjacency entry, the transition and the output. -/
def mkSolver (n : ℕ) (hn : 0 < n) (w : ℕ → ℕ) (init : ℕ → ℕ → ℕ → ℕ)
    (qry : ℕ → ℕ → ℕ × ℕ) (nxt : ℕ → ℕ → Bool → ℕ) (outp : ℕ → ℕ → Option Bool) :
    Solver n where
  State := Fin (w n + 1)
  fin := inferInstance
  init := fun s t => ⟨min (init n s.val t.val) (w n), by omega⟩
  query := fun q => (⟨(qry n q.val).1 % n, Nat.mod_lt _ hn⟩, ⟨(qry n q.val).2 % n, Nat.mod_lt _ hn⟩)
  next := fun q b => ⟨min (nxt n q.val b) (w n), by omega⟩
  out := fun q => outp n q.val

/-- **A uniform form of the statement `SL = L`**: undirected `s`-`t` connectivity is
decided by a *uniformly computable* family of machines using `O(log n)` bits of memory.
Uniformity is expressed here by requiring the numerical description of the machine
family (its size, initial configuration, queries, transitions and outputs) to be
computable.

This `Prop` is stated for reference only; it is not proved in this development.  The
statement in which the family is not required to be computable is `CS.reingold_sl_l`,
which *is* proved here.

Two caveats about the statement itself.  Requiring the description to be computable is
necessary but not sufficient for membership in `L` in the usual sense: the genuine
statement asks for the description to be computable *within logarithmic space* by a
single program, which is what makes Reingold's construction hard, whereas mere
computability of the description can in principle be arranged by an exhaustive search
over the finitely many candidate machines of the allowed size.  Formalising
logarithmic-space computability of the description would require a full space-bounded
machine model for the description itself, which is not developed here. -/
def SLeqL : Prop :=
  ∃ (c : ℕ) (w : ℕ → ℕ) (init : ℕ → ℕ → ℕ → ℕ) (qry : ℕ → ℕ → ℕ × ℕ)
      (nxt : ℕ → ℕ → Bool → ℕ) (outp : ℕ → ℕ → Option Bool),
    Computable w ∧
    Computable (fun p : ℕ × ℕ × ℕ => init p.1 p.2.1 p.2.2) ∧
    Computable (fun p : ℕ × ℕ => qry p.1 p.2) ∧
    Computable (fun p : ℕ × ℕ × Bool => nxt p.1 p.2.1 p.2.2) ∧
    Computable (fun p : ℕ × ℕ => outp p.1 p.2) ∧
    (∀ n, w n ≤ c * n ^ c) ∧
    (∀ n, ∀ hn : 0 < n, (mkSolver n hn w init qry nxt outp).Correct)

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

/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Reingold.Basic

/-!
The transition operator of the lazy walk, its symmetry and positive semidefiniteness.
-/

namespace CS

open Finset

variable {n : ℕ} {A : Fin n → Fin n → Bool}

/-- Standard inner product on `Fin n → ℝ`. -/
def ip (x y : Fin n → ℝ) : ℝ := ∑ u : Fin n, x u * y u

/-- Squared euclidean norm. -/
def nsq (x : Fin n → ℝ) : ℝ := ip x x

/-- The transition operator of the lazy `2n`-regular walk. -/
noncomputable def Pv (A : Fin n → Fin n → Bool) (x : Fin n → ℝ) (u : Fin n) : ℝ :=
  (∑ a : Lab n, x (step A u a)) / (2 * n)

/-- `T`-fold iterate of the transition operator. -/
noncomputable def Pit (A : Fin n → Fin n → Bool) (T : ℕ) (x : Fin n → ℝ) : Fin n → ℝ :=
  (Pv A)^[T] x

lemma ip_comm (x y : Fin n → ℝ) : ip x y = ip y x := by
  unfold ip; exact Finset.sum_congr rfl fun u _ => mul_comm _ _

lemma nsq_nonneg (x : Fin n → ℝ) : 0 ≤ nsq x := by
  unfold nsq ip
  exact Finset.sum_nonneg fun u _ => mul_self_nonneg _

lemma sq_le_nsq (x : Fin n → ℝ) (u : Fin n) : (x u) ^ 2 ≤ nsq x := by
  unfold nsq ip
  have h := Finset.single_le_sum (f := fun v => x v * x v)
    (fun v _ => mul_self_nonneg (x v)) (Finset.mem_univ u)
  simpa [sq] using h

lemma Pv_add (A : Fin n → Fin n → Bool) (x y : Fin n → ℝ) :
    Pv A (x + y) = Pv A x + Pv A y := by
  funext u
  simp only [Pv, Pi.add_apply]
  rw [← add_div]
  congr 1
  simp [Finset.sum_add_distrib]

lemma Pv_smul (A : Fin n → Fin n → Bool) (c : ℝ) (x : Fin n → ℝ) :
    Pv A (c • x) = c • Pv A x := by
  funext u
  simp only [Pv, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

lemma Pv_sub (A : Fin n → Fin n → Bool) (x y : Fin n → ℝ) :
    Pv A (x - y) = Pv A x - Pv A y := by
  funext u
  simp only [Pv, Pi.sub_apply]
  rw [← sub_div]
  congr 1
  simp [Finset.sum_sub_distrib]

/-- Symmetry of the transition operator. -/
lemma ip_Pv (hA : Sym A) (x y : Fin n → ℝ) : ip (Pv A x) y = ip x (Pv A y) := by
  have key : ∑ p : Fin n × Lab n, x (step A p.1 p.2) * y p.1
      = ∑ p : Fin n × Lab n, x p.1 * y (step A p.1 p.2) := by
    have h := sum_rot hA (fun p => x (step A p.1 p.2) * y p.1)
    rw [← h]
    refine Finset.sum_congr rfl fun p _ => ?_
    have h1 : (rot A p).1 = step A p.1 p.2 := rot_fst p
    have h2 : step A (rot A p).1 (rot A p).2 = p.1 := by
      have hh := rot_fst (A := A) (rot A p)
      rw [rot_involutive hA p] at hh
      exact hh.symm
    rw [h2, h1]
  have e1 : ∑ u : Fin n, (∑ a : Lab n, x (step A u a)) / (2 * n) * y u
      = (∑ p : Fin n × Lab n, x (step A p.1 p.2) * y p.1) / (2 * n) := by
    rw [Fintype.sum_prod_type, Finset.sum_div]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [div_mul_eq_mul_div, Finset.sum_mul]
  have e2 : ∑ u : Fin n, x u * ((∑ a : Lab n, y (step A u a)) / (2 * n))
      = (∑ p : Fin n × Lab n, x p.1 * y (step A p.1 p.2)) / (2 * n) := by
    rw [Fintype.sum_prod_type, Finset.sum_div]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_div_assoc', Finset.mul_sum]
  unfold ip Pv
  rw [e1, e2, key]

/-- Sum of squares is preserved by the step reindexing. -/
lemma sum_sq_step (hA : Sym A) (x : Fin n → ℝ) :
    ∑ u : Fin n, ∑ a : Lab n, (x (step A u a)) ^ 2 = (2 * n : ℝ) * nsq x := by
  have h := sum_step_const hA (fun u => (x u) ^ 2)
  rw [h]
  unfold nsq ip
  congr 1
  exact Finset.sum_congr rfl fun u _ => by ring

lemma sum_const_lab (x : Fin n → ℝ) :
    (∑ u : Fin n, ∑ _a : Lab n, (x u) ^ 2) = (2 * n : ℝ) * nsq x := by
  unfold nsq ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (Lab n) : ℝ) = 2 * n := by simp [Lab]
  rw [hc]; ring

/-- The Dirichlet form identity. -/
lemma dirichlet (hA : Sym A) (hn : 0 < n) (x : Fin n → ℝ) :
    nsq x - ip (Pv A x) x
      = (∑ u : Fin n, ∑ a : Lab n, (x u - x (step A u a)) ^ 2) / (4 * n) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have per_u : ∀ u : Fin n, ∑ a : Lab n, (x u - x (step A u a)) ^ 2
      = (∑ _a : Lab n, (x u) ^ 2) - 2 * (∑ a : Lab n, x u * x (step A u a))
        + (∑ a : Lab n, (x (step A u a)) ^ 2) := by
    intro u
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hexp : ∑ u : Fin n, ∑ a : Lab n, (x u - x (step A u a)) ^ 2
      = (∑ u : Fin n, ∑ _a : Lab n, (x u) ^ 2)
        - 2 * (∑ u : Fin n, ∑ a : Lab n, x u * x (step A u a))
        + (∑ u : Fin n, ∑ a : Lab n, (x (step A u a)) ^ 2) := by
    rw [Finset.sum_congr rfl (fun u _ => per_u u), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.mul_sum]
  have h2 : (∑ u : Fin n, ∑ a : Lab n, x u * x (step A u a)) = (2 * n : ℝ) * ip (Pv A x) x := by
    have key : ∀ u : Fin n, (2 * (n:ℝ)) * ((∑ a : Lab n, x (step A u a)) / (2 * n) * x u)
        = ∑ a : Lab n, x u * x (step A u a) := by
      intro u
      have h2n : (2 * (n:ℝ)) ≠ 0 := by positivity
      have hcancel : (2 * (n:ℝ)) * ((∑ a : Lab n, x (step A u a)) / (2 * n) * x u)
          = (∑ a : Lab n, x (step A u a)) * x u := by
        field_simp
      rw [hcancel, Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    unfold ip Pv
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => (key u).symm
  rw [hexp, sum_const_lab, h2, sum_sq_step hA]
  field_simp
  ring

/-- Positive semidefiniteness of the (lazy) transition operator. -/
lemma Pv_psd (hA : Sym A) (hn : 0 < n) (x : Fin n → ℝ) : 0 ≤ ip (Pv A x) x := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hsplit : ∀ u : Fin n, (∑ a : Lab n, x (step A u a))
      = (n : ℝ) * x u + ∑ i : Fin n, x (step A u (true, i)) := by
    intro u
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    have hfalse : ∑ i : Fin n, x (step A u (false, i)) = (n : ℝ) * x u := by
      simp [step, Finset.sum_const]
    rw [hfalse]; ring
  set S : ℝ := ∑ u : Fin n, (∑ i : Fin n, x (step A u (true, i))) * x u with hS
  have hcs : |S| ≤ (n : ℝ) * nsq x := by
    have h1 : S = ∑ p : Fin n × Fin n, x (step A p.1 (true, p.2)) * x p.1 := by
      rw [hS, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun u _ => by rw [Finset.sum_mul]
    have hlazy : ∑ u : Fin n, ∑ _i : Fin n, (x (step A u (false, _i))) ^ 2
        = (n : ℝ) * nsq x := by
      have h : ∀ u : Fin n, ∑ _i : Fin n, (x (step A u (false, _i))) ^ 2 = (n : ℝ) * (x u) ^ 2 := by
        intro u
        simp [step, Finset.sum_const]
      rw [Finset.sum_congr rfl (fun u _ => h u), ← Finset.mul_sum]
      unfold nsq ip
      congr 1
      exact Finset.sum_congr rfl fun u _ => by ring
    have hsplit2 : ∑ u : Fin n, ∑ a : Lab n, (x (step A u a)) ^ 2
        = (∑ u : Fin n, ∑ i : Fin n, (x (step A u (false, i))) ^ 2)
          + ∑ u : Fin n, ∑ i : Fin n, (x (step A u (true, i))) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      ring
    have hsq1 : ∑ p : Fin n × Fin n, (x (step A p.1 (true, p.2))) ^ 2 = (n : ℝ) * nsq x := by
      rw [Fintype.sum_prod_type]
      have hall := sum_sq_step hA x
      rw [hsplit2, hlazy] at hall
      linarith
    have hsq2 : ∑ p : Fin n × Fin n, (x p.1) ^ 2 = (n : ℝ) * nsq x := by
      rw [Fintype.sum_prod_type]
      have h : ∀ u : Fin n, ∑ _i : Fin n, (x u) ^ 2 = (n : ℝ) * (x u) ^ 2 := by
        intro u; simp [Finset.sum_const]
      rw [Finset.sum_congr rfl (fun u _ => h u), ← Finset.mul_sum]
      unfold nsq ip
      congr 1
      exact Finset.sum_congr rfl fun u _ => by ring
    have hcs' := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin n × Fin n))
      (fun p => x (step A p.1 (true, p.2))) (fun p => x p.1)
    rw [← h1] at hcs'
    rw [hsq1, hsq2] at hcs'
    have hnn : 0 ≤ (n : ℝ) * nsq x := mul_nonneg (le_of_lt hn') (nsq_nonneg x)
    nlinarith [abs_nonneg S, sq_abs S]
  have hip : ip (Pv A x) x = ((n : ℝ) * nsq x + S) / (2 * n) := by
    have hterm : ∀ u : Fin n, (∑ a : Lab n, x (step A u a)) / (2 * n) * x u
        = ((n : ℝ) * (x u * x u) + (∑ i : Fin n, x (step A u (true, i))) * x u) / (2 * n) := by
      intro u
      rw [hsplit u]
      ring
    unfold ip Pv
    rw [Finset.sum_congr rfl (fun u _ => hterm u), ← Finset.sum_div]
    congr 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hS]
    rfl
  rw [hip]
  have hSle : -((n : ℝ) * nsq x) ≤ S := neg_le_of_abs_le hcs
  have h2n : (0:ℝ) < 2 * n := by linarith
  apply div_nonneg _ (le_of_lt h2n)
  linarith

end CS

/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Reingold.Operator

/-!
The spectral gap of the lazy walk on a connected component, and the resulting
contraction estimate for the iterated transition operator.
-/

namespace CS

open Finset

open scoped Classical

variable {n : ℕ} {A : Fin n → Fin n → Bool} {s : Fin n}

/-- The connected component of `s`. -/
noncomputable def comp (A : Fin n → Fin n → Bool) (s : Fin n) : Finset (Fin n) :=
  univ.filter (fun v => Conn A s v)

lemma mem_comp {v : Fin n} : v ∈ comp A s ↔ Conn A s v := by
  simp [comp]

/-- The subspace of vectors supported on the component of `s` and summing to zero. -/
def InW (A : Fin n → Fin n → Bool) (s : Fin n) (x : Fin n → ℝ) : Prop :=
  (∀ u, ¬ Conn A s u → x u = 0) ∧ (∑ u ∈ comp A s, x u) = 0

/-- The indicator function of the component of `s`. -/
noncomputable def indC (A : Fin n → Fin n → Bool) (s : Fin n) : Fin n → ℝ :=
  fun u => if Conn A s u then 1 else 0

/-- The indicator function of a single vertex. -/
noncomputable def delta (v : Fin n) : Fin n → ℝ := fun u => if u = v then 1 else 0

lemma step_conn_iff (hA : Sym A) (u : Fin n) (a : Lab n) :
    Conn A s (step A u a) ↔ Conn A s u := by
  constructor
  · intro h
    exact conn_trans h (conn_symm hA (conn_step A u a))
  · intro h
    exact conn_trans h (conn_step A u a)

/-- `Pv` preserves the subspace `W`. -/
lemma Pv_mem_W (hA : Sym A) (hn : 0 < n) {x : Fin n → ℝ} (hx : InW A s x) :
    InW A s (Pv A x) := by
  have hn' : (0:ℝ) < 2 * n := by
    have : (0:ℝ) < n := by exact_mod_cast hn
    linarith
  constructor
  · intro u hu
    have : ∀ a : Lab n, x (step A u a) = 0 := by
      intro a
      exact hx.1 _ (fun h => hu ((step_conn_iff hA u a).1 h))
    simp [Pv, this]
  · -- the total mass is preserved
    have hsupp : ∀ u, ¬ Conn A s u → Pv A x u = 0 := by
      intro u hu
      have : ∀ a : Lab n, x (step A u a) = 0 := by
        intro a
        exact hx.1 _ (fun h => hu ((step_conn_iff hA u a).1 h))
      simp [Pv, this]
    have h1 : ∑ u ∈ comp A s, Pv A x u = ∑ u : Fin n, Pv A x u :=
      Finset.sum_subset (Finset.subset_univ _)
        (fun u _ hu => hsupp u (by simpa [mem_comp] using hu))
    have h2 : ∑ u : Fin n, Pv A x u = ∑ u : Fin n, x u := by
      unfold Pv
      rw [← Finset.sum_div, sum_step_const hA]
      field_simp
    have h3 : ∑ u : Fin n, x u = ∑ u ∈ comp A s, x u :=
      (Finset.sum_subset (Finset.subset_univ _)
        (fun u _ hu => hx.1 u (by simpa [mem_comp] using hu))).symm
    rw [h1, h2, h3, hx.2]

/-! ### A simple graph structure, used to extract simple paths -/

/-- The simple graph attached to the adjacency matrix `A`. -/
def Gr (A : Fin n → Fin n → Bool) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (A u v = true ∨ A v u = true)
  symm := by
    rintro u v ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma adj_A (hA : Sym A) {u v : Fin n} (h : (Gr A).Adj u v) : A u v = true := by
  rcases h.2 with h' | h'
  · exact h'
  · rw [hA]; exact h'

lemma conn_reachable {u v : Fin n} (h : Conn A u v) : (Gr A).Reachable u v := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hbc ih =>
      rcases eq_or_ne b c with rfl | hne
      · exact ih
      · exact ih.trans (SimpleGraph.Adj.reachable ⟨hne, Or.inl hbc⟩)

/-- The Dirichlet energy of `x` for the lazy walk. -/
noncomputable def Dform (A : Fin n → Fin n → Bool) (x : Fin n → ℝ) : ℝ :=
  ∑ u : Fin n, ∑ a : Lab n, (x u - x (step A u a)) ^ 2

lemma Dform_nonneg (A : Fin n → Fin n → Bool) (x : Fin n → ℝ) : 0 ≤ Dform A x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Telescoping the increments of `x` along a walk. -/
lemma telescope (x : Fin n → ℝ) {u v : Fin n} (p : (Gr A).Walk u v) :
    ((p.darts.map (fun d => x d.fst - x d.snd)).sum) = x u - x v := by
  induction p with
  | nil => simp
  | cons h q ih => simp [SimpleGraph.Walk.darts_cons, ih]

/-- Any set of distinct darts contributes at most the full Dirichlet energy. -/
lemma dart_sum_le (hA : Sym A) (x : Fin n → ℝ) (S : Finset ((Gr A).Dart)) :
    ∑ d ∈ S, (x d.fst - x d.snd) ^ 2 ≤ Dform A x := by
  set f : Fin n × Lab n → ℝ := fun p => (x p.1 - x (step A p.1 p.2)) ^ 2 with hf
  have hDf : Dform A x = ∑ p : Fin n × Lab n, f p := by
    rw [Dform, Fintype.sum_prod_type]
  set F : (Gr A).Dart → Fin n × Lab n := fun d => (d.fst, (true, d.snd)) with hF
  have hinj : ∀ d1 ∈ S, ∀ d2 ∈ S, F d1 = F d2 → d1 = d2 := by
    intro d1 _ d2 _ h
    simp only [hF, Prod.mk.injEq] at h
    exact SimpleGraph.Dart.ext _ _ (Prod.ext h.1 h.2.2)
  have hval : ∀ d ∈ S, f (F d) = (x d.fst - x d.snd) ^ 2 := by
    intro d _
    have hstep : step A d.fst (true, d.snd) = d.snd := by
      simp [step, adj_A hA d.adj]
    simp [hf, hF, hstep]
  calc ∑ d ∈ S, (x d.fst - x d.snd) ^ 2 = ∑ d ∈ S, f (F d) :=
        (Finset.sum_congr rfl hval).symm
    _ = ∑ p ∈ S.image F, f p := (Finset.sum_image hinj).symm
    _ ≤ ∑ p : Fin n × Lab n, f p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun p _ _ => by positivity)
    _ = Dform A x := hDf.symm

/-- Along a simple path, Cauchy-Schwarz bounds the squared difference of the endpoint
values by `n` times the Dirichlet energy. -/
lemma diff_sq_le (hA : Sym A) (x : Fin n → ℝ) {u v : Fin n} (h : Conn A u v) :
    (x u - x v) ^ 2 ≤ (n : ℝ) * Dform A x := by
  obtain ⟨w⟩ := conn_reachable (A := A) h
  set p := w.bypass with hp
  have hpath : p.IsPath := w.bypass_isPath
  have hnodup : p.darts.Nodup := SimpleGraph.Walk.darts_nodup_of_support_nodup hpath.support_nodup
  have htel : ∑ d ∈ p.darts.toFinset, (x d.fst - x d.snd) = x u - x v := by
    rw [List.sum_toFinset _ hnodup]
    exact telescope x p
  have hcard : (p.darts.toFinset.card : ℝ) ≤ n := by
    have h1 : p.darts.toFinset.card = p.darts.length := List.toFinset_card_of_nodup hnodup
    have h2 : p.darts.length = p.length := p.length_darts
    have h3 : p.length < Fintype.card (Fin n) := hpath.length_lt
    have h4 : p.darts.toFinset.card ≤ n := by
      rw [h1, h2]; simpa using h3.le
    exact_mod_cast h4
  have hsq := sq_sum_le_card_mul_sum_sq (s := p.darts.toFinset)
    (f := fun d => x d.fst - x d.snd)
  rw [htel] at hsq
  have hle := dart_sum_le hA x p.darts.toFinset
  have hnn : 0 ≤ ∑ d ∈ p.darts.toFinset, (x d.fst - x d.snd) ^ 2 :=
    Finset.sum_nonneg fun d _ => sq_nonneg _
  calc (x u - x v)^2
      ≤ (p.darts.toFinset.card : ℝ) * ∑ d ∈ p.darts.toFinset, (x d.fst - x d.snd)^2 := hsq
    _ ≤ (n : ℝ) * ∑ d ∈ p.darts.toFinset, (x d.fst - x d.snd)^2 :=
        mul_le_mul_of_nonneg_right hcard hnn
    _ ≤ (n : ℝ) * Dform A x := mul_le_mul_of_nonneg_left hle (by positivity)

/-- The Poincaré inequality on the subspace `W`. -/
lemma nsq_le_Dform (hA : Sym A) (hn : 0 < n) {x : Fin n → ℝ} (hx : InW A s x) :
    nsq x ≤ (n:ℝ)^2 * Dform A x := by
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hne : (univ : Finset (Fin n)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fin.pos_iff_nonempty.mp hn
  obtain ⟨w, -, hw⟩ := Finset.exists_max_image (univ : Finset (Fin n)) (fun u => (x u)^2) hne
  have hmax : ∀ u, (x u)^2 ≤ (x w)^2 := fun u => hw u (Finset.mem_univ u)
  have h1 : nsq x ≤ (n:ℝ) * (x w)^2 := by
    have hs : nsq x = ∑ u : Fin n, (x u)^2 := by
      unfold nsq ip; exact Finset.sum_congr rfl fun u _ => by ring
    rw [hs]
    calc ∑ u : Fin n, (x u)^2 ≤ ∑ _u : Fin n, (x w)^2 :=
          Finset.sum_le_sum fun u _ => hmax u
      _ = (n:ℝ) * (x w)^2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : (x w)^2 ≤ (n:ℝ) * Dform A x := by
    rcases eq_or_ne (x w) 0 with h0 | h0
    · rw [h0]
      simpa using mul_nonneg hn0 (Dform_nonneg A x)
    · have hwc : Conn A s w := by
        by_contra hc
        exact h0 (hx.1 w hc)
      have hz : ∃ z ∈ comp A s, x z * x w ≤ 0 := by
        by_contra hcon
        push_neg at hcon
        have hpos : 0 < ∑ z ∈ comp A s, x z * x w :=
          Finset.sum_pos hcon ⟨w, by rw [mem_comp]; exact hwc⟩
        rw [← Finset.sum_mul, hx.2, zero_mul] at hpos
        exact lt_irrefl 0 hpos
      obtain ⟨z, hzc, hzle⟩ := hz
      have hzconn : Conn A w z := conn_trans (conn_symm hA hwc) ((mem_comp).1 hzc)
      have hd := diff_sq_le hA x hzconn
      nlinarith [sq_nonneg (x z), hd]
  calc nsq x ≤ (n:ℝ) * (x w)^2 := h1
    _ ≤ (n:ℝ) * ((n:ℝ) * Dform A x) := mul_le_mul_of_nonneg_left h2 hn0
    _ = (n:ℝ)^2 * Dform A x := by ring

/-- The spectral gap: on the subspace `W` the Rayleigh quotient of the lazy walk is at
most `1 - 1/(4n³)`.  This is the elementary bound coming from the Dirichlet form and a
simple path between an extremal vertex and a vertex of the opposite sign. -/
lemma gap (hA : Sym A) (hn : 0 < n) {x : Fin n → ℝ} (hx : InW A s x) :
    ip (Pv A x) x ≤ (1 - 1 / (4 * (n:ℝ)^3)) * nsq x := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hd : nsq x - ip (Pv A x) x = Dform A x / (4 * n) := dirichlet hA hn x
  have hD := nsq_le_Dform (s := s) hA hn hx
  have hineq : nsq x / (4 * (n:ℝ)^3) ≤ Dform A x / (4 * n) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hD, hnpos]
  have hrw : (1 - 1/(4*(n:ℝ)^3)) * nsq x = nsq x - nsq x/(4*(n:ℝ)^3) := by
    field_simp
  rw [hrw]
  linarith

lemma ip_add_left (x y z : Fin n → ℝ) : ip (x + y) z = ip x z + ip y z := by
  simp [ip, add_mul, Finset.sum_add_distrib]

lemma ip_smul_left (c : ℝ) (x y : Fin n → ℝ) : ip (c • x) y = c * ip x y := by
  simp [ip, Finset.mul_sum, mul_assoc]

lemma ip_add_right (x y z : Fin n → ℝ) : ip x (y + z) = ip x y + ip x z := by
  rw [ip_comm, ip_add_left, ip_comm x y, ip_comm x z]

lemma ip_smul_right (c : ℝ) (x y : Fin n → ℝ) : ip x (c • y) = c * ip x y := by
  rw [ip_comm, ip_smul_left, ip_comm x y]

/-- Cauchy-Schwarz for the positive semidefinite form `(x,y) ↦ ⟪Pv x, y⟫`. -/
lemma cauchy_schwarz_Pv (hA : Sym A) (hn : 0 < n) (x y : Fin n → ℝ) :
    (ip (Pv A x) y) ^ 2 ≤ ip (Pv A x) x * ip (Pv A y) y := by
  have hsym : ip (Pv A y) x = ip (Pv A x) y := by
    rw [ip_Pv hA, ip_comm]
  have key : ∀ t : ℝ, 0 ≤ ip (Pv A y) y * (t * t) + (2 * ip (Pv A x) y) * t + ip (Pv A x) x := by
    intro t
    have := Pv_psd hA hn (x + t • y)
    rw [Pv_add, Pv_smul, ip_add_left, ip_add_right, ip_add_right, ip_smul_left, ip_smul_left,
      ip_smul_right, ip_smul_right, hsym] at this
    nlinarith [this]
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith [hd]

/-- Contraction of one step of the walk on the subspace `W`. -/
lemma nsq_Pv_le (hA : Sym A) (hn : 0 < n) {x : Fin n → ℝ} (hx : InW A s x) :
    nsq (Pv A x) ≤ (1 - 1 / (4 * (n:ℝ)^3)) ^ 2 * nsq x := by
  set M : ℝ := 1 - 1 / (4 * (n:ℝ)^3) with hM
  have hMnn : (0:ℝ) ≤ M := by
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hcube : (1:ℝ) ≤ (n:ℝ)^3 := one_le_pow₀ hn'
    have h4 : 1 / (4 * (n:ℝ)^3) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    simp only [hM]; linarith
  have hy : InW A s (Pv A x) := Pv_mem_W hA hn hx
  have hcs := cauchy_schwarz_Pv hA hn x (Pv A x)
  have h1 : ip (Pv A x) x ≤ M * nsq x := gap hA hn hx
  have h2 : ip (Pv A (Pv A x)) (Pv A x) ≤ M * nsq (Pv A x) := gap hA hn hy
  have hnn2 : 0 ≤ ip (Pv A (Pv A x)) (Pv A x) := Pv_psd hA hn (Pv A x)
  have hcs2 : (nsq (Pv A x))^2 ≤ (M * nsq x) * (M * nsq (Pv A x)) := by
    calc (nsq (Pv A x))^2 = (ip (Pv A x) (Pv A x))^2 := rfl
      _ ≤ ip (Pv A x) x * ip (Pv A (Pv A x)) (Pv A x) := hcs
      _ ≤ (M * nsq x) * (M * nsq (Pv A x)) := by
          apply mul_le_mul h1 h2 hnn2 (by nlinarith [nsq_nonneg x])
  rcases eq_or_lt_of_le (nsq_nonneg (Pv A x)) with h0 | hpos
  · rw [← h0]; exact mul_nonneg (sq_nonneg M) (nsq_nonneg x)
  · have := nsq_nonneg x
    nlinarith [hcs2, hpos]

lemma Pit_zero (A : Fin n → Fin n → Bool) (x : Fin n → ℝ) : Pit A 0 x = x := rfl

lemma Pit_succ (A : Fin n → Fin n → Bool) (T : ℕ) (x : Fin n → ℝ) :
    Pit A (T + 1) x = Pv A (Pit A T x) := by
  unfold Pit
  rw [Function.iterate_succ_apply']

lemma Pit_mem_W (hA : Sym A) (hn : 0 < n) {x : Fin n → ℝ} (hx : InW A s x) (T : ℕ) :
    InW A s (Pit A T x) := by
  induction T with
  | zero => simpa [Pit_zero] using hx
  | succ T ih => rw [Pit_succ]; exact Pv_mem_W hA hn ih

/-- Contraction of the iterated walk operator on `W`. -/
lemma nsq_Pit_le (hA : Sym A) (hn : 0 < n) {x : Fin n → ℝ} (hx : InW A s x) (T : ℕ) :
    nsq (Pit A T x) ≤ ((1 - 1 / (4 * (n:ℝ)^3)) ^ T) ^ 2 * nsq x := by
  induction T with
  | zero => simp [Pit_zero]
  | succ T ih =>
      have h1 := nsq_Pv_le (s := s) hA hn (Pit_mem_W hA hn hx T)
      rw [Pit_succ]
      have hlam : (0:ℝ) ≤ 1 - 1 / (4 * (n:ℝ)^3) := by
        have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
        have hcube : (1:ℝ) ≤ (n:ℝ)^3 := one_le_pow₀ hn'
        have h4 : 1 / (4 * (n:ℝ)^3) ≤ 1 := by
          rw [div_le_one (by linarith)]
          linarith
        linarith
      calc nsq (Pv A (Pit A T x)) ≤ (1 - 1 / (4 * (n:ℝ)^3)) ^ 2 * nsq (Pit A T x) := h1
        _ ≤ (1 - 1 / (4 * (n:ℝ)^3)) ^ 2 * (((1 - 1 / (4 * (n:ℝ)^3)) ^ T) ^ 2 * nsq x) := by
              apply mul_le_mul_of_nonneg_left ih (by positivity)
        _ = ((1 - 1 / (4 * (n:ℝ)^3)) ^ (T+1)) ^ 2 * nsq x := by ring

end CS

/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Reingold.UTS

/-!
The logarithmic space machine for undirected `s`-`t` connectivity: it follows a
universal traversal sequence from `s`, keeping only the current vertex, the target and
the position in the sequence, and accepts as soon as it meets the target.
-/

namespace CS

open Finset

variable {n : ℕ} {A : Fin n → Fin n → Bool}

/-- One step of the walk, with the queried adjacency bit supplied separately. -/
def stepB (a : Lab n) (u : Fin n) (b : Bool) : Fin n :=
  if a.1 = true then (if b = true then a.2 else u) else u

lemma stepB_eq_step (A : Fin n → Fin n → Bool) (a : Lab n) (u : Fin n) :
    stepB a u (A u a.2) = step A u a := by
  unfold stepB step
  by_cases h : a.1 = true <;> simp [h]

/-- The machine following the label sequence `σ` from `s`, accepting as soon as it
reaches `t`.  Its configurations are: a halting configuration carrying the output bit,
or a triple (target, current vertex, position in `σ`). -/
def utsSolver (σ : List (Lab n)) : Solver n where
  State := (Bool × Fin n) ⊕ (Fin n × Fin n × Fin (σ.length + 1))
  fin := inferInstance
  init := fun s t => Sum.inr (t, s, ⟨0, Nat.succ_pos _⟩)
  query := fun q => match q with
    | Sum.inl (_, u) => (u, u)
    | Sum.inr (_, u, i) => (u, (σ.getD i.val (false, u)).2)
  next := fun q b => match q with
    | Sum.inl p => Sum.inl p
    | Sum.inr (t, u, i) =>
        if u = t then Sum.inl (true, u)
        else if h : i.val < σ.length then
          Sum.inr (t, stepB (σ.getD i.val (false, u)) u b, ⟨i.val + 1, by omega⟩)
        else Sum.inl (false, u)
  out := fun q => match q with
    | Sum.inl (b, _) => some b
    | Sum.inr _ => none

lemma utsSolver_card (σ : List (Lab n)) :
    Fintype.card (utsSolver σ).State = 2 * n + n * (n * (σ.length + 1)) := by
  simp [utsSolver]

/-- Before the target is met, the configuration of the machine records the position of
the walk along `σ`. -/
lemma utsSolver_run (σ : List (Lab n)) (A : Fin n → Fin n → Bool) (s t : Fin n) :
    ∀ (j : ℕ) (hj : j ≤ σ.length), (∀ j' < j, walk A s (σ.take j') ≠ t) →
      (utsSolver σ).run A s t j
        = Sum.inr (t, walk A s (σ.take j), ⟨j, Nat.lt_succ_of_le hj⟩) := by
  intro j
  induction j with
  | zero =>
      intro hj _
      simp [Solver.run, utsSolver, walk]
  | succ j ih =>
      intro hj hlt
      have hjle : j ≤ σ.length := by omega
      have hjlt : j < σ.length := by omega
      have hlt' : ∀ j' < j, walk A s (σ.take j') ≠ t := fun j' h => hlt j' (by omega)
      have hrun := ih hjle hlt'
      have hstep : (utsSolver σ).run A s t (j + 1)
          = (utsSolver σ).stepC A ((utsSolver σ).run A s t j) := by
        unfold Solver.run
        rw [Function.iterate_succ_apply']
      set u := walk A s (σ.take j) with hu
      have hut : u ≠ t := hlt j (by omega)
      have hgetD : σ.getD j (false, u) = σ[j] := by
        simp [hjlt]
      have hwalk : walk A s (σ.take (j + 1)) = step A u σ[j] := by
        rw [List.take_add_one]
        simp only [List.getElem?_eq_getElem hjlt, Option.toList_some]
        rw [walk_append, ← hu]
        rfl
      rw [hstep, hrun]
      show (utsSolver σ).next _ _ = _
      simp only [utsSolver, hgetD]
      rw [if_neg hut, dif_pos hjlt]
      simp only [Sum.inr.injEq, Prod.mk.injEq, true_and]
      refine ⟨?_, trivial⟩
      rw [hwalk, ← stepB_eq_step A σ[j] u]

/-- The machine following a universal traversal sequence decides connectivity. -/
lemma utsSolver_correct {σ : List (Lab n)} (hσ : IsUTS σ) :
    (utsSolver σ).Correct := by
  classical
  intro A hA s t
  have hiter : ∀ j : ℕ, (utsSolver σ).run A s t (j + 1)
      = (utsSolver σ).stepC A ((utsSolver σ).run A s t j) := by
    intro j
    unfold Solver.run
    rw [Function.iterate_succ_apply']
  by_cases hconn : Conn A s t
  · obtain ⟨m, hm, hwm⟩ := hσ A hA s t hconn
    have hex : ∃ j, walk A s (σ.take j) = t := ⟨m, hwm⟩
    have hm0 : walk A s (σ.take (Nat.find hex)) = t := Nat.find_spec hex
    have hmin : ∀ j < Nat.find hex, walk A s (σ.take j) ≠ t := fun j hj => Nat.find_min hex hj
    have hm0le : Nat.find hex ≤ σ.length := le_trans (Nat.find_le hwm) hm
    refine ⟨true, ⟨Nat.find hex + 1, ?_, ?_⟩, by simp [hconn]⟩
    · intro j hj
      have hjle : j ≤ Nat.find hex := by omega
      rw [utsSolver_run σ A s t j (le_trans hjle hm0le)
        (fun j' h => hmin j' (lt_of_lt_of_le h hjle))]
      rfl
    · rw [hiter, utsSolver_run σ A s t (Nat.find hex) hm0le hmin]
      show (utsSolver σ).out ((utsSolver σ).next _ _) = _
      simp [utsSolver, hm0]
  · have hne : ∀ j, walk A s (σ.take j) ≠ t := by
      intro j h
      exact hconn (h ▸ conn_walk A s (σ.take j))
    refine ⟨false, ⟨σ.length + 1, ?_, ?_⟩, by simp [hconn]⟩
    · intro j hj
      rw [utsSolver_run σ A s t j (by omega) (fun j' _ => hne j')]
      rfl
    · rw [hiter, utsSolver_run σ A s t σ.length le_rfl (fun j' _ => hne j')]
      show (utsSolver σ).out ((utsSolver σ).next _ _) = _
      have hu := hne σ.length
      simp only [utsSolver]
      rw [if_neg hu, dif_neg (lt_irrefl σ.length)]

/-- **Undirected `s`-`t` connectivity in logarithmic space (nonuniform).**

There is a constant `c` such that for every `n` there is a machine with at most
`c * n ^ c` configurations — that is, using `O(log n)` bits of memory — which reads the
adjacency matrix of an `n`-vertex undirected graph one bit at a time and decides
whether two given vertices are connected. -/
theorem ustcon_logspace :
    ∃ c : ℕ, ∀ n : ℕ, 0 < n → ∃ M : Solver n,
      Fintype.card M.State ≤ c * n ^ c ∧ M.Correct := by
  refine ⟨100, fun n hn => ?_⟩
  obtain ⟨σ, hlen, hσ⟩ := exists_uts (n := n) hn
  refine ⟨utsSolver σ, ?_, utsSolver_correct hσ⟩
  have hL : σ.length ≤ 64 * n ^ 7 := hlen ▸ utsLen_le hn
  have hcard := utsSolver_card σ
  have h1 : 1 ≤ n := hn
  calc Fintype.card (utsSolver σ).State = 2 * n + n * (n * (σ.length + 1)) := hcard
    _ ≤ 2 * n + n * (n * (64 * n ^ 7 + 1)) := by
        have := Nat.add_le_add_right hL 1
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)) _
    _ ≤ 100 * n ^ 100 := by
        have hpow : n ^ 9 ≤ n ^ 100 := Nat.pow_le_pow_right h1 (by norm_num)
        have hn2 : n ≤ n ^ 9 := Nat.le_self_pow (by norm_num) n
        have hn3 : n * n ≤ n ^ 9 := by
          calc n * n = n ^ 2 := by ring
            _ ≤ n ^ 9 := Nat.pow_le_pow_right h1 (by norm_num)
        have hn4 : n * (n * (64 * n ^ 7)) = 64 * n ^ 9 := by ring
        nlinarith [hpow, hn2, hn3]

end CS

/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Reingold.Setup

/-!
Elementary properties of the rotation map, of connectivity and of label sequences.
-/

namespace CS

open Finset

variable {n : ℕ} {A : Fin n → Fin n → Bool}

@[simp] lemma rot_fst (p : Fin n × Lab n) : (rot A p).1 = step A p.1 p.2 := by
  unfold rot step
  by_cases h : p.2.1 = true
  · by_cases h2 : A p.1 p.2.2 = true <;> simp [h, h2]
  · simp [h]

lemma rot_involutive (hA : Sym A) : Function.Involutive (rot A) := by
  rintro ⟨u, b, i⟩
  by_cases hb : b = true
  · subst hb
    by_cases h : A u i = true
    · have h' : A i u = true := by rw [hA]; exact h
      simp [rot, h, h']
    · simp [rot, h]
  · simp [rot, hb]

/-- The equivalence of `Fin n × Lab n` with itself given by the rotation map. -/
def rotEquiv (hA : Sym A) : (Fin n × Lab n) ≃ (Fin n × Lab n) :=
  Function.Involutive.toPerm _ (rot_involutive hA)

lemma sum_rot (hA : Sym A) (f : Fin n × Lab n → ℝ) :
    ∑ p : Fin n × Lab n, f (rot A p) = ∑ p : Fin n × Lab n, f p :=
  Fintype.sum_equiv (rotEquiv hA) _ _ (fun _ => rfl)

/-- Reindexing along the rotation map: summing `g (step u a)` over all `(u,a)` is the
same as summing `g u`, i.e. the walk is a `2n`-regular multigraph. -/
lemma sum_step (hA : Sym A) (g : Fin n → ℝ) :
    ∑ u : Fin n, ∑ a : Lab n, g (step A u a) = ∑ u : Fin n, ∑ _a : Lab n, g u := by
  have h1 : ∑ p : Fin n × Lab n, g (step A p.1 p.2) = ∑ p : Fin n × Lab n, g p.1 := by
    have := sum_rot hA (fun p => g p.1)
    simpa using this
  simpa [Fintype.sum_prod_type] using h1

lemma sum_step_const (hA : Sym A) (g : Fin n → ℝ) :
    ∑ u : Fin n, ∑ a : Lab n, g (step A u a) = (2 * n : ℝ) * ∑ u : Fin n, g u := by
  rw [sum_step hA]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
  have hc : (Fintype.card (Lab n) : ℝ) = 2 * n := by simp [Lab]
  rw [hc]

/-! ### Connectivity -/

lemma conn_refl (A : Fin n → Fin n → Bool) (u : Fin n) : Conn A u u :=
  Relation.ReflTransGen.refl

lemma conn_trans {u v w : Fin n} (h1 : Conn A u v) (h2 : Conn A v w) : Conn A u w :=
  Relation.ReflTransGen.trans h1 h2

lemma conn_of_adj {u v : Fin n} (h : A u v = true) : Conn A u v :=
  Relation.ReflTransGen.single h

lemma conn_symm (hA : Sym A) {u v : Fin n} (h : Conn A u v) : Conn A v u := by
  refine Relation.ReflTransGen.symmetric ?_ h
  intro a b hab
  rw [hA]; exact hab

lemma conn_step (A : Fin n → Fin n → Bool) (u : Fin n) (a : Lab n) :
    Conn A u (step A u a) := by
  unfold step
  by_cases hb : a.1 = true
  · by_cases h : A u a.2 = true
    · simpa [hb, h] using conn_of_adj h
    · simpa [hb, h] using conn_refl A u
  · simpa [hb] using conn_refl A u

lemma conn_walk (A : Fin n → Fin n → Bool) (u : Fin n) (σ : List (Lab n)) :
    Conn A u (walk A u σ) := by
  induction σ generalizing u with
  | nil => simp [walk]; exact conn_refl A u
  | cons a σ ih =>
      have : walk A u (a :: σ) = walk A (step A u a) σ := by simp [walk]
      rw [this]
      exact conn_trans (conn_step A u a) (ih _)

/-! ### Label sequences -/

lemma walk_nil (A : Fin n → Fin n → Bool) (u : Fin n) : walk A u [] = u := rfl

lemma walk_cons (A : Fin n → Fin n → Bool) (u : Fin n) (a : Lab n) (σ : List (Lab n)) :
    walk A u (a :: σ) = walk A (step A u a) σ := rfl

lemma walk_append (A : Fin n → Fin n → Bool) (u : Fin n) (σ τ : List (Lab n)) :
    walk A u (σ ++ τ) = walk A (walk A u σ) τ := by
  simp [walk, List.foldl_append]

lemma mem_seqs {m : ℕ} {σ : List (Lab n)} : σ ∈ seqs n m ↔ σ.length = m := by
  induction m generalizing σ with
  | zero => simp [seqs, List.length_eq_zero_iff]
  | succ m ih =>
      constructor
      · intro h
        simp only [seqs, Finset.mem_biUnion, Finset.mem_image] at h
        obtain ⟨a, -, τ, hτ, rfl⟩ := h
        simp [ih.1 hτ]
      · intro h
        cases σ with
        | nil => simp at h
        | cons a τ =>
            simp only [seqs, Finset.mem_biUnion, Finset.mem_image]
            exact ⟨a, Finset.mem_univ _, τ, ih.2 (by simpa using h), rfl⟩

lemma card_seqs (m : ℕ) : (seqs n m).card = (2 * n) ^ m := by
  induction m with
  | zero => simp [seqs]
  | succ m ih =>
      have hdisj : ∀ a ∈ (univ : Finset (Lab n)), ∀ b ∈ (univ : Finset (Lab n)), a ≠ b →
          Disjoint ((seqs n m).image (a :: ·)) ((seqs n m).image (b :: ·)) := by
        intro a _ b _ hab
        simp only [Finset.disjoint_left, Finset.mem_image]
        rintro σ ⟨τ, -, rfl⟩ ⟨τ', -, h⟩
        exact hab (by simpa using (List.cons.injEq _ _ _ _ ▸ h).1.symm)
      have : (seqs n (m + 1)).card
          = ∑ _a : Lab n, ((seqs n m).image (fun τ => _a :: τ)).card := by
        simp only [seqs]
        exact Finset.card_biUnion hdisj
      rw [this]
      have himg : ∀ a : Lab n, ((seqs n m).image (fun τ => a :: τ)).card = (seqs n m).card := by
        intro a
        apply Finset.card_image_of_injective
        intro x y hxy
        simpa using hxy
      simp only [himg, ih, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      have : Fintype.card (Lab n) = 2 * n := by simp [Lab]
      rw [this]
      ring

end CS

/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Reingold.Hitting

/-!
Existence of polynomially long universal traversal sequences, by the probabilistic
method: block by block, the walk fails to reach a prescribed vertex of its component
with probability at most `1 - 1/(2n)`, and a union bound over all symmetric graphs and
all pairs of vertices leaves a sequence that works for all of them.
-/

namespace CS

open Finset

open scoped Classical

variable {n : ℕ} {A : Fin n → Fin n → Bool}

/-- Length of one block of the traversal sequence. -/
def blockLen (n : ℕ) : ℕ := 8 * n ^ 4

/-- Number of blocks of the traversal sequence. -/
def numBlocks (n : ℕ) : ℕ := 2 * n * (n + 1) ^ 2

/-- Length of the universal traversal sequence constructed below. -/
def utsLen (n : ℕ) : ℕ := numBlocks n * blockLen n

lemma blockLen_pos (hn : 0 < n) : 0 < blockLen n := by
  unfold blockLen; positivity

lemma utsLen_le (hn : 0 < n) : utsLen n ≤ 64 * n ^ 7 := by
  unfold utsLen numBlocks blockLen
  have h : (n + 1) ^ 2 ≤ 4 * n ^ 2 := by nlinarith
  calc 2 * n * (n + 1) ^ 2 * (8 * n ^ 4) ≤ 2 * n * (4 * n ^ 2) * (8 * n ^ 4) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)
    _ = 64 * n ^ 7 := by ring

/-- The sequences of length `k * T` along which the walk started at `u` misses `v` at
every block boundary. -/
noncomputable def badSet (A : Fin n → Fin n → Bool) (u v : Fin n) (k T : ℕ) :
    Finset (List (Lab n)) :=
  (seqs n (k * T)).filter (fun σ => ∀ j ≤ k, walk A u (σ.take (j * T)) ≠ v)

/-- The block estimate: each block independently reaches `v` with probability at least
`1/(2n)`, so the number of sequences missing `v` at every block boundary decays
geometrically. -/
lemma badSet_card_le (hA : Sym A) {v : Fin n} {T : ℕ}
    (hcount : ∀ u : Fin n, Conn A u v →
      (2 * n) ^ (T - 1) ≤ ((seqs n T).filter (fun β => walk A u β = v)).card) :
    ∀ (k : ℕ) (u : Fin n), Conn A u v →
      (badSet A u v k T).card ≤ ((2 * n) ^ T - (2 * n) ^ (T - 1)) ^ k := by
  classical
  set R : ℕ := (2 * n) ^ T - (2 * n) ^ (T - 1) with hR
  intro k
  induction k with
  | zero =>
      intro u _
      have h : (badSet A u v 0 T).card ≤ (seqs n (0 * T)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      simpa [card_seqs] using h
  | succ k ih =>
      intro u hu
      set G : Finset (List (Lab n)) := (seqs n T).filter (fun β => walk A u β ≠ v) with hG
      have hmap : ∀ σ ∈ badSet A u v (k + 1) T,
          (⟨σ.take T, σ.drop T⟩ : (_ : List (Lab n)) × List (Lab n))
            ∈ G.sigma (fun β => badSet A (walk A u β) v k T) := by
        intro σ hσ
        rw [badSet, Finset.mem_filter, mem_seqs] at hσ
        obtain ⟨hlen, hmiss⟩ := hσ
        have hlenT : (σ.take T).length = T := by
          rw [List.length_take, hlen]
          have : T ≤ (k + 1) * T := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
          omega
        have hlenD : (σ.drop T).length = k * T := by
          rw [List.length_drop, hlen]
          have : (k + 1) * T = T + k * T := by ring
          omega
        have hblock : walk A u (σ.take T) ≠ v := by
          have := hmiss 1 (by omega)
          simpa using this
        rw [Finset.mem_sigma]
        refine ⟨?_, ?_⟩
        · rw [hG, Finset.mem_filter, mem_seqs]
          exact ⟨hlenT, hblock⟩
        · rw [badSet, Finset.mem_filter, mem_seqs]
          refine ⟨hlenD, ?_⟩
          intro j hj
          have hsplit : σ.take ((j + 1) * T) = σ.take T ++ (σ.drop T).take (j * T) := by
            have : (j + 1) * T = T + j * T := by ring
            rw [this, List.take_add]
          have := hmiss (j + 1) (by omega)
          rw [hsplit, walk_append] at this
          exact this
      have hinj : Set.InjOn (fun σ : List (Lab n) => (⟨σ.take T, σ.drop T⟩ :
          (_ : List (Lab n)) × List (Lab n))) (badSet A u v (k + 1) T) := by
        intro x _ y _ h
        have h1 : x.take T = y.take T := congrArg Sigma.fst h
        have h2 : x.drop T = y.drop T := by
          simpa [h1] using congrArg Sigma.snd h
        calc x = x.take T ++ x.drop T := (List.take_append_drop _ _).symm
          _ = y.take T ++ y.drop T := by rw [h1, h2]
          _ = y := List.take_append_drop _ _
      have hcard := Finset.card_le_card_of_injOn _ hmap hinj
      rw [Finset.card_sigma] at hcard
      have hterm : ∀ β ∈ G, (badSet A (walk A u β) v k T).card ≤ R ^ k := by
        intro β hβ
        refine ih _ ?_
        exact conn_trans (conn_symm hA (conn_walk A u β)) hu
      have hsum : ∑ β ∈ G, (badSet A (walk A u β) v k T).card ≤ G.card * R ^ k := by
        calc ∑ β ∈ G, (badSet A (walk A u β) v k T).card ≤ ∑ _β ∈ G, R ^ k :=
              Finset.sum_le_sum hterm
          _ = G.card * R ^ k := by rw [Finset.sum_const, smul_eq_mul]
      have hGcard : G.card ≤ R := by
        have hpart := Finset.card_filter_add_card_filter_not
          (s := seqs n T) (p := fun β => walk A u β = v)
        rw [card_seqs] at hpart
        have hge := hcount u hu
        have hGeq : G = (seqs n T).filter (fun β => ¬ (walk A u β = v)) := by
          rw [hG]
        rw [hGeq, hR]
        omega
      calc (badSet A u v (k + 1) T).card ≤ ∑ β ∈ G, (badSet A (walk A u β) v k T).card := hcard
        _ ≤ G.card * R ^ k := hsum
        _ ≤ R * R ^ k := Nat.mul_le_mul_right _ hGcard
        _ = R ^ (k + 1) := by ring

/-- A half-life estimate for the per-block failure probability. -/
lemma half_pow_bound (hn : 0 < n) : (1 - 1 / (2 * (n:ℝ))) ^ (2 * n) ≤ 1 / 2 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0:ℝ) < 2 * n := by linarith
  have hle : 1 - 1 / (2 * (n:ℝ)) ≤ Real.exp (-(1 / (2 * (n:ℝ)))) := by
    have := Real.add_one_le_exp (-(1 / (2 * (n:ℝ))))
    linarith
  have hbase : (0:ℝ) ≤ 1 - 1 / (2 * (n:ℝ)) := by
    have : 1 / (2 * (n:ℝ)) ≤ 1 := by
      rw [div_le_one hpos]; linarith
    linarith
  have hpow : (1 - 1 / (2 * (n:ℝ))) ^ (2 * n) ≤ (Real.exp (-(1 / (2 * (n:ℝ))))) ^ (2 * n) :=
    pow_le_pow_left₀ hbase hle _
  have hexp : (Real.exp (-(1 / (2 * (n:ℝ))))) ^ (2 * n) = Real.exp (-1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hexp2 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have h2 : (2:ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    have := (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0:ℝ) < 2)).2 h2
    linarith [this]
  calc (1 - 1 / (2 * (n:ℝ))) ^ (2 * n) ≤ (Real.exp (-(1 / (2 * (n:ℝ))))) ^ (2 * n) := hpow
    _ = Real.exp (-1) := hexp
    _ ≤ 1 / 2 := hexp2

/-- The union bound is strict. -/
lemma uts_counting (hn : 0 < n) :
    2 ^ (n * n) * n * n *
        ((2 * n) ^ blockLen n - (2 * n) ^ (blockLen n - 1)) ^ numBlocks n
      < (2 * n) ^ utsLen n := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hNpos : (0:ℝ) < 2 * n := by linarith
  set T : ℕ := blockLen n with hTdef
  set k : ℕ := numBlocks n with hkdef
  have hT1 : 1 ≤ T := by
    rw [hTdef, blockLen]
    have : 1 ≤ n ^ 4 := Nat.one_le_pow _ _ hn
    omega
  have hNle : ((2 * n) ^ (T - 1) : ℕ) ≤ (2 * n) ^ T :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hbase : (0:ℝ) ≤ 1 - 1 / (2 * (n:ℝ)) := by
    have : 1 / (2 * (n:ℝ)) ≤ 1 := by
      rw [div_le_one hNpos]; linarith
    linarith
  -- the scalar estimate
  have hkey : ((2:ℝ) ^ (n * n) * n * n) * (1 - 1 / (2 * (n:ℝ))) ^ k < 1 := by
    have hk : k = (2 * n) * (n + 1) ^ 2 := by rw [hkdef, numBlocks]
    have hhalf : (1 - 1 / (2 * (n:ℝ))) ^ k ≤ (1 / 2) ^ ((n + 1) ^ 2) := by
      rw [hk, pow_mul]
      exact pow_le_pow_left₀ (by positivity) (half_pow_bound hn) _
    have hnlt : (n : ℝ) < 2 ^ n := by
      have : n < 2 ^ n := Nat.lt_two_pow_self
      exact_mod_cast this
    have hnn : (n:ℝ) * n < 2 ^ n * 2 ^ n := by
      have h0 : (0:ℝ) < n := by linarith
      nlinarith
    have hcount : (2:ℝ) ^ (n * n) * n * n < 2 ^ ((n + 1) ^ 2) := by
      have hp1 : (0:ℝ) < 2 ^ (n * n) := by positivity
      calc (2:ℝ) ^ (n * n) * n * n = 2 ^ (n * n) * ((n:ℝ) * n) := by ring
        _ < 2 ^ (n * n) * (2 ^ n * 2 ^ n) := mul_lt_mul_of_pos_left hnn hp1
        _ = 2 ^ (n * n + (n + n)) := by ring
        _ < 2 ^ (n * n + (n + n) + 1) := by
            apply pow_lt_pow_right₀ (by norm_num)
            omega
        _ = 2 ^ ((n + 1) ^ 2) := by ring_nf
    have hhalfpos : (0:ℝ) < (1 / 2 : ℝ) ^ ((n + 1) ^ 2) := by positivity
    have hnn0 : (0:ℝ) ≤ (2:ℝ) ^ (n * n) * n * n := by positivity
    calc ((2:ℝ) ^ (n * n) * n * n) * (1 - 1 / (2 * (n:ℝ))) ^ k
        ≤ ((2:ℝ) ^ (n * n) * n * n) * (1 / 2) ^ ((n + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hhalf hnn0
      _ < 2 ^ ((n + 1) ^ 2) * (1 / 2) ^ ((n + 1) ^ 2) :=
          mul_lt_mul_of_pos_right hcount hhalfpos
      _ = 1 := by rw [← mul_pow]; norm_num
  have hfac : (2 * (n:ℝ)) ^ T - (2 * (n:ℝ)) ^ (T - 1)
      = (2 * (n:ℝ)) ^ T * (1 - 1 / (2 * n)) := by
    have h1 : (2 * (n:ℝ)) ^ T = (2 * (n:ℝ)) ^ (T - 1) * (2 * n) := by
      rw [← pow_succ]
      congr 1
      omega
    field_simp
    rw [h1]
    ring
  have hposT : (0:ℝ) < ((2 * (n:ℝ)) ^ T) ^ k := by positivity
  have hmain : ((2:ℝ) ^ (n * n) * n * n) * ((2 * (n:ℝ)) ^ T - (2 * (n:ℝ)) ^ (T - 1)) ^ k
      < (2 * (n:ℝ)) ^ (k * T) := by
    rw [hfac, mul_pow, show (2 * (n:ℝ)) ^ (k * T) = ((2 * (n:ℝ)) ^ T) ^ k from pow_mul' _ _ _]
    calc ((2:ℝ) ^ (n * n) * n * n) * (((2 * (n:ℝ)) ^ T) ^ k * (1 - 1 / (2 * (n:ℝ))) ^ k)
        = (((2:ℝ) ^ (n * n) * n * n) * (1 - 1 / (2 * (n:ℝ))) ^ k) * ((2 * (n:ℝ)) ^ T) ^ k := by
          ring
      _ < 1 * ((2 * (n:ℝ)) ^ T) ^ k := mul_lt_mul_of_pos_right hkey hposT
      _ = ((2 * (n:ℝ)) ^ T) ^ k := one_mul _
  have hcast1 : ((2 ^ (n * n) * n * n * ((2 * n) ^ T - (2 * n) ^ (T - 1)) ^ k : ℕ) : ℝ)
      = ((2:ℝ) ^ (n * n) * n * n) * ((2 * (n:ℝ)) ^ T - (2 * (n:ℝ)) ^ (T - 1)) ^ k := by
    push_cast [Nat.cast_sub hNle]
    ring
  have hcast2 : (((2 * n) ^ utsLen n : ℕ) : ℝ) = (2 * (n:ℝ)) ^ (k * T) := by
    rw [show utsLen n = k * T from rfl]
    push_cast
    ring
  rw [← Nat.cast_lt (α := ℝ), hcast1, hcast2]
  exact hmain


/-- **Existence of universal traversal sequences.**  For every `n ≥ 1` there is a label
sequence of length `utsLen n = O(n⁷)` which traverses every connected component of
every undirected graph on `n` vertices, from every starting point. -/
theorem exists_uts (hn : 0 < n) :
    ∃ σ : List (Lab n), σ.length = utsLen n ∧ IsUTS σ := by
  classical
  set T : ℕ := blockLen n with hTdef
  set k : ℕ := numBlocks n with hkdef
  set R : ℕ := (2 * n) ^ T - (2 * n) ^ (T - 1) with hR
  set Tri : Finset ((Fin n → Fin n → Bool) × Fin n × Fin n) :=
    univ.filter (fun p => Sym p.1 ∧ Conn p.1 p.2.1 p.2.2) with hTri
  set Bad : ((Fin n → Fin n → Bool) × Fin n × Fin n) → Finset (List (Lab n)) :=
    fun p => badSet p.1 p.2.1 p.2.2 k T with hBad
  have hbadle : ∀ p ∈ Tri, (Bad p).card ≤ R ^ k := by
    intro p hp
    rw [hTri, Finset.mem_filter] at hp
    obtain ⟨-, hsym, hconn⟩ := hp
    refine badSet_card_le hsym ?_ k p.2.1 hconn
    intro u hu
    rw [hTdef, blockLen]
    exact hit_count hsym hn hu
  have hTricard : Tri.card ≤ 2 ^ (n * n) * n * n := by
    have h1 : Tri.card ≤ Fintype.card ((Fin n → Fin n → Bool) × Fin n × Fin n) := by
      rw [← Finset.card_univ]
      exact Finset.card_le_univ Tri
    have hcardfun : Fintype.card (Fin n → Fin n → Bool) = 2 ^ (n * n) := by
      rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul]
    have h2 : Fintype.card ((Fin n → Fin n → Bool) × Fin n × Fin n) = 2 ^ (n * n) * n * n := by
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, hcardfun, mul_assoc]
    omega
  have hunion : (Tri.biUnion Bad).card < (seqs n (utsLen n)).card := by
    have h1 : (Tri.biUnion Bad).card ≤ ∑ p ∈ Tri, (Bad p).card := Finset.card_biUnion_le
    have h2 : ∑ p ∈ Tri, (Bad p).card ≤ Tri.card * R ^ k := by
      calc ∑ p ∈ Tri, (Bad p).card ≤ ∑ _p ∈ Tri, R ^ k := Finset.sum_le_sum hbadle
        _ = Tri.card * R ^ k := by rw [Finset.sum_const, smul_eq_mul]
    have h3 : Tri.card * R ^ k ≤ 2 ^ (n * n) * n * n * R ^ k :=
      Nat.mul_le_mul_right _ hTricard
    have h4 : 2 ^ (n * n) * n * n * R ^ k < (2 * n) ^ utsLen n := by
      rw [hR, hTdef, hkdef]
      exact uts_counting hn
    rw [card_seqs]
    omega
  obtain ⟨σ, hσmem, hσbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hunion
  refine ⟨σ, mem_seqs.1 hσmem, ?_⟩
  intro A hA s v hconn
  have hp : ((A, s, v) : (Fin n → Fin n → Bool) × Fin n × Fin n) ∈ Tri := by
    rw [hTri, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hA, hconn⟩
  have hnot : σ ∉ Bad (A, s, v) := fun h => hσbad (Finset.mem_biUnion.2 ⟨_, hp, h⟩)
  rw [hBad] at hnot
  simp only [badSet, Finset.mem_filter, mem_seqs, not_and, not_forall] at hnot
  have hlen : σ.length = k * T := by
    rw [mem_seqs.1 hσmem]
    rfl
  obtain ⟨j, hj⟩ := hnot hlen
  obtain ⟨hjk, hjv⟩ := hj
  refine ⟨j * T, ?_, not_not.1 hjv⟩
  rw [hlen]
  exact Nat.mul_le_mul_right _ hjk

end CS

/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
Basic setup: undirected graphs given by a symmetric adjacency predicate on `Fin n`,
the associated lazy `2n`-regular walk given by a rotation map, connectivity, label
sequences, and the space-bounded machine model.
-/

namespace CS

open Finset

/-- Labels for the lazy walk on an `n`-vertex graph: `(false, i)` is a lazy step
(stay put), `(true, i)` is an attempt to move to vertex `i`. -/
abbrev Lab (n : ℕ) : Type := Bool × Fin n

variable {n : ℕ}

/-- Symmetry of an adjacency predicate. -/
def Sym (A : Fin n → Fin n → Bool) : Prop := ∀ u v, A u v = A v u

/-- One step of the lazy walk: from `u` with label `a`. -/
def step (A : Fin n → Fin n → Bool) (u : Fin n) (a : Lab n) : Fin n :=
  if a.1 = true then (if A u a.2 = true then a.2 else u) else u

/-- The rotation map of the lazy `2n`-regular multigraph attached to `A`.  It is an
involution of `Fin n × Lab n` whose first component is `step`. -/
def rot (A : Fin n → Fin n → Bool) (p : Fin n × Lab n) : Fin n × Lab n :=
  if p.2.1 = true then (if A p.1 p.2.2 = true then (p.2.2, (true, p.1)) else p) else p

/-- Connectivity: reflexive transitive closure of the adjacency relation. -/
def Conn (A : Fin n → Fin n → Bool) (u v : Fin n) : Prop :=
  Relation.ReflTransGen (fun a b => A a b = true) u v

/-- The walk determined by a list of labels. -/
def walk (A : Fin n → Fin n → Bool) (u : Fin n) (σ : List (Lab n)) : Fin n :=
  σ.foldl (step A) u

/-- All label sequences of a given length. -/
def seqs (n : ℕ) : ℕ → Finset (List (Lab n))
  | 0 => {[]}
  | m + 1 => (univ : Finset (Lab n)).biUnion fun a => (seqs n m).image (a :: ·)

/-- A sequence `σ` is a *universal traversal sequence* if, for every symmetric graph `A`
on `Fin n` and every pair `s, v` of connected vertices, the walk following `σ` from `s`
visits `v`. -/
def IsUTS (σ : List (Lab n)) : Prop :=
  ∀ A : Fin n → Fin n → Bool, Sym A → ∀ s v : Fin n, Conn A s v →
    ∃ m ≤ σ.length, walk A s (σ.take m) = v

/-! ### The space-bounded machine model -/

/-- A deterministic machine with a finite configuration space `State`, reading the
adjacency matrix of an `n`-vertex graph one bit at a time.  The initial configuration
is determined by the two distinguished vertices `s`, `t`; in each configuration the
machine queries one entry of the adjacency matrix and moves to a new configuration
depending on the answer; halting configurations carry an output bit.

The *space* used by the machine is `log₂ (card State)`; a machine is a logarithmic
space machine when `card State ≤ n ^ c` for a constant `c` independent of `n`. -/
structure Solver (n : ℕ) where
  /-- The configuration space. -/
  State : Type
  /-- Finiteness of the configuration space. -/
  fin : Fintype State
  /-- Initial configuration on distinguished vertices `s`, `t`. -/
  init : Fin n → Fin n → State
  /-- The adjacency entry queried in a configuration. -/
  query : State → Fin n × Fin n
  /-- The transition function. -/
  next : State → Bool → State
  /-- Output of a halting configuration. -/
  out : State → Option Bool

attribute [instance] Solver.fin

namespace Solver

variable (M : Solver n) (A : Fin n → Fin n → Bool)

/-- One computation step on the input graph `A`. -/
def stepC (q : M.State) : M.State :=
  M.next q (A (M.query q).1 (M.query q).2)

/-- The configuration after `k` steps. -/
def run (s t : Fin n) (k : ℕ) : M.State :=
  (M.stepC A)^[k] (M.init s t)

/-- The machine outputs `b` on input `(A, s, t)`: it halts for the first time after
`k` steps, with output `b`. -/
def Outputs (s t : Fin n) (b : Bool) : Prop :=
  ∃ k, (∀ j < k, M.out (M.run A s t j) = none) ∧ M.out (M.run A s t k) = some b

end Solver

/-- A solver is correct if, on every symmetric adjacency matrix and every pair of
vertices, it halts and its output bit says whether the two vertices are connected. -/
def Solver.Correct (M : Solver n) : Prop :=
  ∀ A : Fin n → Fin n → Bool, Sym A → ∀ s t : Fin n,
    ∃ b : Bool, M.Outputs A s t b ∧ (b = true ↔ Conn A s t)

end CS

/-
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Reingold.Gap

/-!
From the spectral gap to a hitting estimate: after `T = 8n⁴` steps the lazy walk is at
any prescribed vertex of its component with probability at least `1/(2n)`.  Translated
into counting, at least a `1/(2n)` fraction of all label blocks of length `T` drive the
walk from `u` to `v`.
-/

namespace CS

open Finset

open scoped Classical

variable {n : ℕ} {A : Fin n → Fin n → Bool} {s : Fin n}

lemma Pit_add (A : Fin n → Fin n → Bool) (T : ℕ) (x y : Fin n → ℝ) :
    Pit A T (x + y) = Pit A T x + Pit A T y := by
  induction T with
  | zero => simp [Pit_zero]
  | succ T ih => rw [Pit_succ, Pit_succ, Pit_succ, ih, Pv_add]

lemma Pit_smul (A : Fin n → Fin n → Bool) (T : ℕ) (c : ℝ) (x : Fin n → ℝ) :
    Pit A T (c • x) = c • Pit A T x := by
  induction T with
  | zero => simp [Pit_zero]
  | succ T ih => rw [Pit_succ, Pit_succ, ih, Pv_smul]

lemma Pit_sub (A : Fin n → Fin n → Bool) (T : ℕ) (x y : Fin n → ℝ) :
    Pit A T (x - y) = Pit A T x - Pit A T y := by
  induction T with
  | zero => simp [Pit_zero]
  | succ T ih => rw [Pit_succ, Pit_succ, Pit_succ, ih, Pv_sub]

/-- The indicator of a connected component is invariant under the walk operator. -/
lemma Pv_indC (hA : Sym A) (hn : 0 < n) : Pv A (indC A s) = indC A s := by
  funext u
  have hn' : (0:ℝ) < 2 * n := by
    have : (0:ℝ) < n := by exact_mod_cast hn
    linarith
  by_cases hu : Conn A s u
  · have : ∀ a : Lab n, indC A s (step A u a) = 1 := by
      intro a
      simp [indC, (step_conn_iff hA u a).2 hu]
    simp only [Pv, this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hc : (Fintype.card (Lab n) : ℝ) = 2 * n := by simp [Lab]
    rw [hc, indC]
    simp [hu, div_self (ne_of_gt hn')]
  · have hzero : ∀ a : Lab n, indC A s (step A u a) = 0 := by
      intro a
      have hna : ¬ Conn A s (step A u a) := fun h => hu ((step_conn_iff hA u a).1 h)
      simp [indC, hna]
    simp only [Pv, hzero, Finset.sum_const_zero, zero_div]
    simp [indC, hu]

lemma Pit_indC (hA : Sym A) (hn : 0 < n) (T : ℕ) : Pit A T (indC A s) = indC A s := by
  induction T with
  | zero => simp [Pit_zero]
  | succ T ih => rw [Pit_succ, ih, Pv_indC hA hn]

/-- The centred indicator of a vertex lies in the subspace `W`. -/
lemma comp_card_pos (A : Fin n → Fin n → Bool) (s : Fin n) : 0 < (comp A s).card :=
  Finset.card_pos.2 ⟨s, mem_comp.2 (conn_refl A s)⟩

lemma sum_indC (A : Fin n → Fin n → Bool) (s : Fin n) :
    ∑ u ∈ comp A s, indC A s u = ((comp A s).card : ℝ) := by
  have h : ∀ u ∈ comp A s, indC A s u = 1 := fun u hu => by simp [indC, mem_comp.1 hu]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma centred_mem_W {v : Fin n} (hv : Conn A s v) :
    InW A s (delta v - ((comp A s).card : ℝ)⁻¹ • indC A s) := by
  have hc : (0:ℝ) < (comp A s).card := by exact_mod_cast comp_card_pos A s
  constructor
  · intro u hu
    have h1 : delta v u = 0 := by
      have : u ≠ v := fun h => hu (h ▸ hv)
      simp [delta, this]
    have h2 : indC A s u = 0 := by simp [indC, hu]
    simp [h1, h2]
  · have hdelta : ∑ u ∈ comp A s, delta v u = 1 := by
      rw [Finset.sum_eq_single v]
      · simp [delta]
      · intro b _ hb
        simp [delta, hb]
      · intro h
        exact absurd (mem_comp.2 hv) h
    have hpt : ∀ u : Fin n, (delta v - ((comp A s).card : ℝ)⁻¹ • indC A s) u
        = delta v u - ((comp A s).card : ℝ)⁻¹ * indC A s u := fun u => rfl
    simp only [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, hdelta, sum_indC]
    field_simp
    ring

lemma nsq_centred_le_one {v : Fin n} (hv : Conn A s v) :
    nsq (delta v - ((comp A s).card : ℝ)⁻¹ • indC A s) ≤ 1 := by
  classical
  set c : ℝ := ((comp A s).card : ℝ) with hcdef
  have hc : (0:ℝ) < c := by
    rw [hcdef]; exact_mod_cast comp_card_pos A s
  set x : Fin n → ℝ := delta v - c⁻¹ • indC A s with hx
  have hzero : ∀ u, u ∉ comp A s → x u * x u = 0 := by
    intro u hu
    have hnc : ¬ Conn A s u := fun h => hu (mem_comp.2 h)
    have h1 : delta v u = 0 := by
      have : u ≠ v := fun h => hnc (h ▸ hv)
      simp [delta, this]
    have h2 : indC A s u = 0 := by simp [indC, hnc]
    simp [hx, h1, h2]
  have hsum : nsq x = ∑ u ∈ comp A s, x u * x u := by
    unfold nsq ip
    exact (Finset.sum_subset (Finset.subset_univ _) (fun u _ hu => hzero u hu)).symm
  have hterm : ∀ u ∈ comp A s, x u * x u = (delta v u) * (delta v u)
      - 2 * c⁻¹ * delta v u + c⁻¹ * c⁻¹ := by
    intro u hu
    have h2 : indC A s u = 1 := by simp [indC, mem_comp.1 hu]
    simp [hx, h2]
    ring
  have hdelta : ∑ u ∈ comp A s, delta v u = 1 := by
    rw [Finset.sum_eq_single v]
    · simp [delta]
    · intro b _ hb; simp [delta, hb]
    · intro h; exact absurd (mem_comp.2 hv) h
  have hdelta2 : ∑ u ∈ comp A s, (delta v u) * (delta v u) = 1 := by
    rw [Finset.sum_eq_single v]
    · simp [delta]
    · intro b _ hb; simp [delta, hb]
    · intro h; exact absurd (mem_comp.2 hv) h
  rw [hsum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    hdelta2, ← Finset.mul_sum, hdelta]
  rw [Finset.sum_const, nsmul_eq_mul, ← hcdef]
  have : c * (c⁻¹ * c⁻¹) = c⁻¹ := by field_simp
  rw [this]
  have : (0:ℝ) < c⁻¹ := by positivity
  linarith

/-- The contraction factor to the power `8n⁴` is at most `1/(2n)`. -/
lemma lambda_pow_le (hn : 0 < n) :
    (1 - 1 / (4 * (n:ℝ)^3)) ^ (8 * n ^ 4) ≤ 1 / (2 * n) := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hcube : (1:ℝ) ≤ (n:ℝ)^3 := one_le_pow₀ hn1
  set g : ℝ := 1 / (4 * (n:ℝ)^3) with hg
  have hgpos : 0 < g := by rw [hg]; positivity
  have hgle : g ≤ 1 := by
    rw [hg, div_le_one (by linarith)]
    linarith
  have hbase : (0:ℝ) ≤ 1 - g := by linarith
  have h1p : (0:ℝ) < 1 + g := by linarith
  have hstep : 1 - g ≤ (1 + g)⁻¹ := by
    have hmul : (1 - g) * (1 + g) ≤ 1 := by nlinarith
    calc 1 - g = ((1 - g) * (1 + g)) / (1 + g) := by field_simp
      _ ≤ 1 / (1 + g) := by gcongr
      _ = (1 + g)⁻¹ := one_div _
  have hpow : (1 - g) ^ (8 * n ^ 4) ≤ ((1 + g)⁻¹) ^ (8 * n ^ 4) :=
    pow_le_pow_left₀ hbase hstep _
  have hbern : 1 + (8 * n ^ 4 : ℕ) * g ≤ (1 + g) ^ (8 * n ^ 4) :=
    one_add_mul_le_pow (by linarith) _
  have hgT : ((8 * n ^ 4 : ℕ) : ℝ) * g = 2 * n := by
    rw [hg]
    push_cast
    field_simp
    ring
  have hbig : 2 * (n:ℝ) ≤ (1 + g) ^ (8 * n ^ 4) := by
    calc 2 * (n:ℝ) ≤ 1 + 2 * n := by linarith
      _ = 1 + ((8 * n ^ 4 : ℕ) : ℝ) * g := by rw [hgT]
      _ ≤ (1 + g) ^ (8 * n ^ 4) := hbern
  have h2n : (0:ℝ) < 2 * n := by linarith
  have hfinal : ((1 + g)⁻¹) ^ (8 * n ^ 4) ≤ 1 / (2 * n) := by
    calc ((1 + g)⁻¹) ^ (8 * n ^ 4) = ((1 + g) ^ (8 * n ^ 4))⁻¹ := by rw [inv_pow]
      _ ≤ (2 * (n:ℝ))⁻¹ := by gcongr
      _ = 1 / (2 * n) := (one_div _).symm
  exact le_trans hpow hfinal

/-- Hitting estimate: after `8n⁴` steps, the walk started at `s` is at `v` with
probability at least `1/(2n)`, for any `v` in the component of `s`. -/
lemma hit_prob (hA : Sym A) (hn : 0 < n) {v : Fin n} (hv : Conn A s v) :
    1 / (2 * (n:ℝ)) ≤ Pit A (8 * n ^ 4) (delta v) s := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  set c : ℝ := ((comp A s).card : ℝ) with hcdef
  have hcpos : (0:ℝ) < c := by rw [hcdef]; exact_mod_cast comp_card_pos A s
  have hcle : c ≤ (n:ℝ) := by
    rw [hcdef]
    have : (comp A s).card ≤ n := by
      simpa using Finset.card_le_univ (comp A s)
    exact_mod_cast this
  set f : Fin n → ℝ := delta v - c⁻¹ • indC A s with hf
  have hfW : InW A s f := centred_mem_W hv
  have hdecomp : delta v = f + c⁻¹ • indC A s := by
    rw [hf]; abel
  have hind : indC A s s = 1 := by simp [indC, conn_refl A s]
  have hPit : Pit A (8 * n ^ 4) (delta v) s = Pit A (8 * n ^ 4) f s + c⁻¹ := by
    rw [hdecomp, Pit_add, Pit_smul, Pit_indC hA hn]
    simp [hind]
  set lam : ℝ := 1 - 1 / (4 * (n:ℝ)^3) with hlam
  have hlam0 : (0:ℝ) ≤ lam := by
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hcube : (1:ℝ) ≤ (n:ℝ)^3 := one_le_pow₀ hn1
    rw [hlam]
    have : 1 / (4 * (n:ℝ)^3) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  have hnsq : nsq (Pit A (8 * n ^ 4) f) ≤ (lam ^ (8 * n ^ 4)) ^ 2 := by
    have h1 := nsq_Pit_le (s := s) hA hn hfW (8 * n ^ 4)
    have h2 : nsq f ≤ 1 := nsq_centred_le_one hv
    have h3 : (0:ℝ) ≤ (lam ^ (8 * n ^ 4)) ^ 2 := by positivity
    nlinarith [nsq_nonneg f]
  have hsq : (Pit A (8 * n ^ 4) f s) ^ 2 ≤ (lam ^ (8 * n ^ 4)) ^ 2 :=
    le_trans (sq_le_nsq _ s) hnsq
  have hlamT0 : (0:ℝ) ≤ lam ^ (8 * n ^ 4) := pow_nonneg hlam0 _
  have hlamT : lam ^ (8 * n ^ 4) ≤ 1 / (2 * n) := lambda_pow_le hn
  have hlow : -(1 / (2 * (n:ℝ))) ≤ Pit A (8 * n ^ 4) f s := by
    nlinarith [hsq, hlamT0, hlamT]
  have hinv : 1 / (n:ℝ) ≤ c⁻¹ := by
    rw [one_div, inv_le_inv₀ hn' hcpos]
    exact hcle
  have hhalf : 1 / (2 * (n:ℝ)) + 1 / (2 * (n:ℝ)) = 1 / (n:ℝ) := by
    field_simp
    ring
  rw [hPit]
  linarith

/-- Counting version of the walk distribution: the number of label sequences of length
`T` driving the walk from `u` to `v` is `(2n)^T` times the corresponding entry of the
`T`-th power of the transition operator. -/
lemma count_walk_split (A : Fin n → Fin n → Bool) (T : ℕ) (u v : Fin n) :
    ((seqs n (T + 1)).filter (fun σ => walk A u σ = v)).card
      = ∑ a : Lab n, ((seqs n T).filter (fun τ => walk A (step A u a) τ = v)).card := by
  classical
  have himg : ∀ a : Lab n,
      ((seqs n T).image (fun τ => a :: τ)).filter (fun σ => walk A u σ = v)
        = ((seqs n T).filter (fun τ => walk A (step A u a) τ = v)).image (fun τ => a :: τ) := by
    intro a
    ext σ
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨τ, hτ, rfl⟩, hw⟩
      exact ⟨τ, ⟨hτ, by rwa [walk_cons] at hw⟩, rfl⟩
    · rintro ⟨τ, ⟨hτ, hw⟩, rfl⟩
      exact ⟨⟨τ, hτ, rfl⟩, by rw [walk_cons]; exact hw⟩
  have hinj : ∀ a : Lab n, Function.Injective (fun τ : List (Lab n) => a :: τ) := by
    intro a x y h
    simpa using h
  have hdisj : ∀ a ∈ (univ : Finset (Lab n)), ∀ b ∈ (univ : Finset (Lab n)), a ≠ b →
      Disjoint (((seqs n T).image (fun τ => a :: τ)).filter (fun σ => walk A u σ = v))
        (((seqs n T).image (fun τ => b :: τ)).filter (fun σ => walk A u σ = v)) := by
    intro a _ b _ hab
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_image]
    rintro σ ⟨⟨τ, -, rfl⟩, -⟩ ⟨⟨τ', -, h⟩, -⟩
    exact hab (by simpa using (List.cons_eq_cons.1 h).1.symm)
  have hseq : seqs n (T + 1)
      = (univ : Finset (Lab n)).biUnion (fun a => (seqs n T).image (fun τ => a :: τ)) := rfl
  rw [hseq, Finset.filter_biUnion]
  rw [Finset.card_biUnion (fun a ha b hb hab => hdisj a ha b hb hab)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [himg a, Finset.card_image_of_injective _ (hinj a)]

lemma count_walk_eq (A : Fin n → Fin n → Bool) (T : ℕ) (u v : Fin n) :
    ((((seqs n T).filter (fun σ => walk A u σ = v)).card : ℝ))
      = (2 * n) ^ T * Pit A T (delta v) u := by
  classical
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) u.isLt
  have hn' : (0:ℝ) < 2 * n := by
    have : (0:ℝ) < n := by exact_mod_cast hn
    linarith
  induction T generalizing u with
  | zero =>
      have : (seqs n 0).filter (fun σ => walk A u σ = v)
          = if u = v then {([] : List (Lab n))} else ∅ := by
        by_cases h : u = v <;> simp [seqs, walk, h, Finset.filter_singleton]
      rw [this]
      by_cases h : u = v <;> simp [Pit_zero, delta, h]
  | succ T ih =>
      rw [count_walk_split A T u v]
      have hstep : Pit A (T + 1) (delta v) u
          = (∑ a : Lab n, Pit A T (delta v) (step A u a)) / (2 * n) := by
        rw [Pit_succ]
        rfl
      rw [hstep]
      push_cast
      rw [Finset.sum_congr rfl (fun a _ => ih (step A u a)), ← Finset.mul_sum]
      field_simp
      ring

/-- Counting version of the hitting estimate. -/
lemma hit_count (hA : Sym A) (hn : 0 < n) {u v : Fin n} (hv : Conn A u v) :
    (2 * n) ^ (8 * n ^ 4 - 1)
      ≤ (((seqs n (8 * n ^ 4)).filter (fun σ => walk A u σ = v)).card) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h2n : (0:ℝ) < 2 * n := by linarith
  have hT : 1 ≤ 8 * n ^ 4 := by
    have : 1 ≤ n ^ 4 := Nat.one_le_pow _ _ hn
    omega
  have hreal := count_walk_eq A (8 * n ^ 4) u v
  have hp := hit_prob (s := u) hA hn hv
  have hsplit : (2 * (n:ℝ)) ^ (8 * n ^ 4) = (2 * (n:ℝ)) ^ (8 * n ^ 4 - 1) * (2 * n) := by
    rw [← pow_succ]
    congr 1
    omega
  have key : (2 * (n:ℝ)) ^ (8 * n ^ 4 - 1)
      ≤ (((seqs n (8 * n ^ 4)).filter (fun σ => walk A u σ = v)).card : ℝ) := by
    rw [hreal]
    calc (2 * (n:ℝ)) ^ (8 * n ^ 4 - 1)
        = (2 * (n:ℝ)) ^ (8 * n ^ 4) * (1 / (2 * n)) := by
          rw [hsplit]; field_simp
      _ ≤ (2 * (n:ℝ)) ^ (8 * n ^ 4) * Pit A (8 * n ^ 4) (delta v) u := by
          apply mul_le_mul_of_nonneg_left hp (by positivity)
  exact_mod_cast key

end CS

