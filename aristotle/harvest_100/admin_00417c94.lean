/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` to precede any module docstring, so the header above is a
plain block comment; the same text is repeated as the module docstring below.)
-/

import Mathlib

/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## What is formalised here

The statement "there are problems with no fastest algorithm" is formalised as follows.

* `CS.BlumMeasure` is a Blum complexity measure on a programming system: an effective
  numbering of the partial computable functions (`sem_partrec`, `sem_complete`) together with a
  cost function satisfying Blum's two axioms, namely that the cost of a run is defined exactly
  when the run converges (`cost_dom`) and that the graph of the cost function is computable
  (`cost_decidable`).
* `CS.blum` is such a measure. Its semantics is the standard one: a program is a pair `(c, k)`
  of a code `c` in the standard system `Nat.Partrec.Code` and a *compression level* `k`, and it
  computes the function computed by `c`. Its cost is the number of steps of `c` (the least fuel
  making `Nat.Partrec.Code.evaln` converge) recorded on the scale of the `k`-th branch of the
  Ackermann function; at level `0` this is exactly the step count (`CS.scaledCost_level_zero`),
  and along any program the cost still tends to infinity (`CS.scaledCost_unbounded`).
* `CS.hardProblem` is a `0-1` valued computable problem which is arbitrarily hard for the
  standard step count: every algorithm for it exceeds any prescribed primitive recursive time
  bound on infinitely many inputs (`CS.hardProblem_hard_of_primrec`).
* `CS.blum_speedup` combines these: there is a Blum complexity measure and a (hard) decision
  problem such that every algorithm for the problem is beaten, by any prescribed primitive
  recursive factor and on almost every input, by another algorithm for the same problem.

## Scope

Blum's original speedup theorem is stronger in two respects: it holds for *every* Blum
complexity measure (in particular for the standard step count) and for every total computable
speedup factor, at the price of a much more delicate construction of the problem. What is proved
here is the existential statement, for an explicitly constructed Blum measure and primitive
recursive speedup factors; in that measure `CS.blum_no_fastest` shows that in fact no problem
has a fastest algorithm.
-/

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-! ## Blum complexity measures -/

/-- A *Blum complexity measure* on a programming system whose semantics is given by
`sem : Prog → ℕ →. ℕ`.

* `sem_partrec` says that the programming system is effective (there is a universal machine);
* `sem_complete` says that every partial computable function is computed by some program
  (so the system really is a programming system for the partial computable functions);
* `cost_dom` is Blum's first axiom: the cost of a run is defined exactly when the run converges;
* `cost_decidable` is Blum's second axiom: the graph of the cost function is computable. -/
structure BlumMeasure (Prog : Type) [Primcodable Prog] where
  /-- semantics: the partial function computed by a program -/
  sem : Prog → ℕ →. ℕ
  /-- the cost (running time) of a program on an input -/
  cost : Prog → ℕ →. ℕ
  sem_partrec : Partrec₂ sem
  sem_complete : ∀ f : ℕ →. ℕ, Partrec f → ∃ p, sem p = f
  cost_dom : ∀ p n, (cost p n).Dom ↔ (sem p n).Dom
  cost_decidable : ∃ D : Prog × ℕ × ℕ → Bool, Computable D ∧
      ∀ p n m, (D (p, n, m) = true ↔ m ∈ cost p n)

variable {Prog : Type} [Primcodable Prog]

/-- Program `q` beats program `p` by the factor `r`: on almost every input, applying `r` to the
cost of `q` still does not exceed the cost of `p`. -/
def BlumMeasure.SpeedsUp (M : BlumMeasure Prog) (r : ℕ → ℕ) (p q : Prog) : Prop :=
  ∃ N, ∀ n, N ≤ n → ∀ a ∈ M.cost q n, ∀ b ∈ M.cost p n, r a ≤ b

/-- The problem `f` has *no fastest algorithm*: every program for `f` is beaten, by any
prescribed primitive recursive factor `r`, by another program for `f`. -/
def BlumMeasure.NoFastestAlgorithm (M : BlumMeasure Prog) (f : ℕ →. ℕ) : Prop :=
  ∀ p, M.sem p = f → ∀ r : ℕ → ℕ, Nat.Primrec r → ∃ q, M.sem q = f ∧ M.SpeedsUp r p q

/-! ## Step counting for the standard programming system -/

/-- `halts c n f = true` iff the code `c` converges on input `n` with fuel `f`. -/
def halts (c : Code) (n f : ℕ) : Bool := (evaln f c n).isSome

theorem halts_iff_exists {c : Code} {n f : ℕ} : halts c n f = true ↔ ∃ x, x ∈ evaln f c n := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact Option.isSome_iff_exists.2 ⟨x, hx⟩

theorem halts_mono {c : Code} {n f₁ f₂ : ℕ} (h : f₁ ≤ f₂) (h1 : halts c n f₁ = true) :
    halts c n f₂ = true := by
  obtain ⟨x, hx⟩ := halts_iff_exists.1 h1
  exact halts_iff_exists.2 ⟨x, evaln_mono h hx⟩

theorem primrec_halts : Primrec fun x : (Code × ℕ) × ℕ => halts x.1.1 x.1.2 x.2 :=
  Primrec.option_isSome.comp (primrec_evaln.comp
    ((Primrec.snd.pair (Primrec.fst.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.fst)))

/-- The step count of `c` on `n`: the least fuel making the computation converge. -/
noncomputable def stepCount (c : Code) (n : ℕ) : Part ℕ :=
  Nat.rfind fun f => Part.some (halts c n f)

theorem mem_stepCount {c : Code} {n s : ℕ} :
    s ∈ stepCount c n ↔ halts c n s = true ∧ ∀ t < s, halts c n t = false := by
  rw [stepCount, Nat.mem_rfind]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(Part.mem_some_iff.1 h1).symm, fun t ht => (Part.mem_some_iff.1 (h2 ht)).symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Part.mem_some_iff.2 h1.symm, fun {t} ht => Part.mem_some_iff.2 (h2 t ht).symm⟩

theorem halts_iff_stepCount {c : Code} {n f : ℕ} :
    halts c n f = true ↔ ∃ s ∈ stepCount c n, s ≤ f := by
  classical
  constructor
  · intro h
    have hex : ∃ t, halts c n t = true := ⟨f, h⟩
    refine ⟨Nat.find hex, ?_, Nat.find_le h⟩
    exact mem_stepCount.2 ⟨Nat.find_spec hex, fun t ht => by simpa using Nat.find_min hex ht⟩
  · rintro ⟨s, hs, hsf⟩
    exact halts_mono hsf (mem_stepCount.1 hs).1

theorem stepCount_dom {c : Code} {n : ℕ} : (stepCount c n).Dom ↔ (eval c n).Dom := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := Part.dom_iff_mem.1 h
    obtain ⟨x, hx⟩ := halts_iff_exists.1 (mem_stepCount.1 hs).1
    exact Part.dom_iff_mem.2 ⟨x, evaln_sound hx⟩
  · intro h
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 h
    obtain ⟨k, hk⟩ := evaln_complete.1 hx
    obtain ⟨s, hs, _⟩ := halts_iff_stepCount.1 (halts_iff_exists.2 ⟨x, hk⟩)
    exact Part.dom_iff_mem.2 ⟨s, hs⟩

theorem input_lt_of_mem_stepCount {c : Code} {n s : ℕ} (h : s ∈ stepCount c n) : n < s := by
  obtain ⟨x, hx⟩ := halts_iff_exists.1 (mem_stepCount.1 h).1
  exact evaln_bound hx

/-! ## A Blum measure with compression levels

A program is a pair `(c, k)` consisting of a code `c` and a *compression level* `k`; it computes
the same function as `c`, but its running time is recorded on the coarser scale given by the
`k`-th branch `ack k` of the Ackermann function: the cost is the largest `y` with
`ack k y ≤ steps`. Both Blum axioms hold for this measure. -/

/-- The cost of the program `(c, k)` on input `n`. -/
noncomputable def scaledCost (p : Code × ℕ) (n : ℕ) : Part ℕ :=
  (stepCount p.1 n).map fun s => Nat.findGreatest (fun y => ack p.2 y ≤ s) s

theorem findGreatest_ack_pos {k s : ℕ} (h : 0 < Nat.findGreatest (fun y => ack k y ≤ s) s) :
    ack k (Nat.findGreatest (fun y => ack k y ≤ s) s) ≤ s := by
  by_contra hc
  rcases Classical.em (∃ n, 0 < n ∧ n ≤ s ∧ ack k n ≤ s) with ⟨n0, h0, h1, h2⟩ | hno
  · exact hc (Nat.findGreatest_spec (P := fun y => ack k y ≤ s) h1 h2)
  · have : Nat.findGreatest (fun y => ack k y ≤ s) s = 0 :=
      Nat.findGreatest_eq_zero_iff.2 fun n hn hns hp => hno ⟨n, hn, hns, hp⟩
    omega

theorem lt_ack_findGreatest_succ {k s : ℕ} :
    s < ack k (Nat.findGreatest (fun y => ack k y ≤ s) s + 1) := by
  by_contra hc
  push_neg at hc
  have h1 : Nat.findGreatest (fun y => ack k y ≤ s) s + 1 ≤ s :=
    le_trans (le_of_lt (lt_ack_right k _)) hc
  have := Nat.le_findGreatest (P := fun y => ack k y ≤ s) h1 hc
  omega

theorem findGreatest_ack_eq {k s m : ℕ} :
    Nat.findGreatest (fun y => ack k y ≤ s) s = m ↔ (m = 0 ∨ ack k m ≤ s) ∧ s < ack k (m + 1) := by
  constructor
  · rintro rfl
    refine ⟨?_, lt_ack_findGreatest_succ⟩
    rcases Nat.eq_zero_or_pos (Nat.findGreatest (fun y => ack k y ≤ s) s) with h | h
    · exact Or.inl h
    · exact Or.inr (findGreatest_ack_pos h)
  · rintro ⟨h1, h2⟩
    have hle : m ≤ Nat.findGreatest (fun y => ack k y ≤ s) s := by
      rcases h1 with rfl | h1
      · exact Nat.zero_le _
      · exact Nat.le_findGreatest (le_trans (le_of_lt (lt_ack_right k m)) h1) h1
    have hge : Nat.findGreatest (fun y => ack k y ≤ s) s ≤ m := by
      rcases Nat.eq_zero_or_pos (Nat.findGreatest (fun y => ack k y ≤ s) s) with h | h
      · omega
      · have hp := findGreatest_ack_pos h
        have h3 : ack k (Nat.findGreatest (fun y => ack k y ≤ s) s) < ack k (m + 1) :=
          lt_of_le_of_lt hp h2
        have := (ack_lt_iff_right (m := k)).1 h3
        omega
    omega

theorem mem_scaledCost_eq {c : Code} {k n m : ℕ} :
    m ∈ scaledCost (c, k) n ↔
      ∃ s ∈ stepCount c n, Nat.findGreatest (fun y => ack k y ≤ s) s = m :=
  Part.mem_map_iff _

theorem mem_scaledCost {c : Code} {k n m : ℕ} :
    m ∈ scaledCost (c, k) n ↔
      ∃ s ∈ stepCount c n, (m = 0 ∨ ack k m ≤ s) ∧ s < ack k (m + 1) := by
  rw [mem_scaledCost_eq]
  constructor
  · rintro ⟨s, hs, hfg⟩
    exact ⟨s, hs, findGreatest_ack_eq.1 hfg⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, findGreatest_ack_eq.2 h⟩

/-- The decision procedure witnessing Blum's second axiom for `scaledCost`. -/
def costDecide (x : (Code × ℕ) × ℕ × ℕ) : Bool :=
  halts x.1.1 x.2.1 (ack x.1.2 (x.2.2 + 1) - 1) &&
    (x.2.2 == 0 || !halts x.1.1 x.2.1 (ack x.1.2 x.2.2 - 1))

theorem computable_costDecide : Computable costDecide := by
  have hc : Computable fun x : (Code × ℕ) × ℕ × ℕ => x.1.1 := Computable.fst.comp Computable.fst
  have hn : Computable fun x : (Code × ℕ) × ℕ × ℕ => x.2.1 := Computable.fst.comp Computable.snd
  have hk : Computable fun x : (Code × ℕ) × ℕ × ℕ => x.1.2 := Computable.snd.comp Computable.fst
  have hm : Computable fun x : (Code × ℕ) × ℕ × ℕ => x.2.2 := Computable.snd.comp Computable.snd
  have hA : Computable fun x : (Code × ℕ) × ℕ × ℕ => ack x.1.2 x.2.2 - 1 :=
    Primrec.nat_sub.to_comp.comp (computable₂_ack.comp hk hm) (Computable.const 1)
  have hB : Computable fun x : (Code × ℕ) × ℕ × ℕ => ack x.1.2 (x.2.2 + 1) - 1 :=
    Primrec.nat_sub.to_comp.comp
      (computable₂_ack.comp hk (Computable.succ.comp hm)) (Computable.const 1)
  have hpA : Computable fun x : (Code × ℕ) × ℕ × ℕ => ((x.1.1, x.2.1), ack x.1.2 x.2.2 - 1) :=
    (hc.pair hn).pair hA
  have hpB : Computable fun x : (Code × ℕ) × ℕ × ℕ =>
      ((x.1.1, x.2.1), ack x.1.2 (x.2.2 + 1) - 1) := (hc.pair hn).pair hB
  have h1 := primrec_halts.to_comp.comp hpB
  have h2 := primrec_halts.to_comp.comp hpA
  have h3 : Computable fun x : (Code × ℕ) × ℕ × ℕ => (x.2.2 == 0) :=
    ((Primrec.nat_casesOn (Primrec.snd.comp Primrec.snd) (Primrec.const true)
      ((Primrec.const false).to₂)).of_eq (by intro x; cases h : x.2.2 <;> simp)).to_comp
  have h4 := (Primrec.dom_bool (!·)).to_comp.comp h2
  have h5 := (Primrec.dom_bool₂ (· || ·)).to_comp.comp h3 h4
  exact (Primrec.dom_bool₂ (· && ·)).to_comp.comp h1 h5

theorem costDecide_iff (p : Code × ℕ) (n m : ℕ) :
    costDecide (p, n, m) = true ↔ m ∈ scaledCost p n := by
  obtain ⟨c, k⟩ := p
  rw [mem_scaledCost]
  simp only [costDecide, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨s, hs, hsle⟩ := halts_iff_stepCount.1 h1
    have hpos : 0 < ack k (m + 1) := ack_pos _ _
    refine ⟨s, hs, ?_, by omega⟩
    rcases h2 with rfl | h2
    · exact Or.inl rfl
    · refine Or.inr ?_
      by_contra hlt
      push_neg at hlt
      have hpos' : 0 < ack k m := ack_pos _ _
      have : halts c n (ack k m - 1) = true :=
        halts_mono (by omega) (mem_stepCount.1 hs).1
      rw [h2] at this
      exact Bool.false_ne_true this
  · rintro ⟨s, hs, hc1, hc2⟩
    have hhalt : halts c n s = true := (mem_stepCount.1 hs).1
    have hpos : 0 < ack k (m + 1) := ack_pos _ _
    refine ⟨halts_mono (by omega) hhalt, ?_⟩
    rcases hc1 with rfl | hc1
    · exact Or.inl rfl
    · refine Or.inr ?_
      by_contra hcon
      have hcon' : halts c n (ack k m - 1) = true := by
        simpa using hcon
      obtain ⟨s', hs', hs'le⟩ := halts_iff_stepCount.1 hcon'
      have hss : s' = s := Part.mem_unique hs' hs
      subst hss
      have := ack_pos k m
      omega

/-- The Blum complexity measure used below: the standard programming system of all partial
computable functions, with programs carrying a compression level. -/
noncomputable def blum : BlumMeasure (Code × ℕ) where
  sem p := eval p.1
  cost := scaledCost
  sem_partrec := eval_part.comp (Computable.fst.comp Computable.fst) Computable.snd
  sem_complete := fun f hf => by
    obtain ⟨c, hc⟩ := exists_code.1 (Partrec.nat_iff.1 hf)
    exact ⟨(c, 0), hc⟩
  cost_dom := fun p n => stepCount_dom
  cost_decidable := ⟨costDecide, computable_costDecide, fun p n m => costDecide_iff p n m⟩

/-- In the measure `blum`, no program is fastest: every program for a problem is beaten,
by any primitive recursive factor, by another program for the same problem. -/
theorem blum_no_fastest (f : ℕ →. ℕ) : blum.NoFastestAlgorithm f := by
  rintro ⟨c, k⟩ hp r hr
  obtain ⟨m₀, hm₀⟩ := exists_lt_ack_of_nat_primrec hr
  set k' := max k m₀ + 2 with hk'
  refine ⟨(c, k'), hp, ⟨ack k' 1, ?_⟩⟩
  intro n hn a ha b hb
  obtain ⟨s, hs, ha1, ha2⟩ := mem_scaledCost.1 ha
  obtain ⟨s', hs', hb1⟩ := mem_scaledCost_eq.1 hb
  have hss : s' = s := Part.mem_unique hs' hs
  rw [hss] at hb1
  have hns : n < s := input_lt_of_mem_stepCount hs
  have hane : a ≠ 0 := by
    rintro rfl
    rw [zero_add] at ha2
    omega
  have hacka : ack k' a ≤ s := by
    rcases ha1 with h | h
    · exact absurd h hane
    · exact h
  have hlt : ack k (ack m₀ a) < ack k' a := ack_ack_lt_ack_max_add_two k m₀ a
  have hz : ack k (ack m₀ a) ≤ s := le_of_lt (lt_of_lt_of_le hlt hacka)
  have hzs : ack m₀ a ≤ s := le_trans (le_of_lt (lt_ack_right k _)) hz
  have : ack m₀ a ≤ Nat.findGreatest (fun y => ack k y ≤ s) s :=
    Nat.le_findGreatest hzs hz
  rw [hb1] at this
  exact le_of_lt (lt_of_lt_of_le (hm₀ a) this)

/-! ## The measure is not degenerate

Two sanity checks on `blum`. First, at compression level `0` the cost is literally the number of
steps (minus one), i.e. the standard step-counting measure is part of the system. Second, costs
do not collapse: along any program, the cost tends to infinity, so the speedups above are not
obtained by costs bottoming out at a fixed value. -/

theorem scaledCost_level_zero {c : Code} {n s : ℕ} (hs : s ∈ stepCount c n) :
    s - 1 ∈ scaledCost (c, 0) n := by
  have hs1 : 1 ≤ s := by
    have := input_lt_of_mem_stepCount hs
    omega
  refine mem_scaledCost.2 ⟨s, hs, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (s - 1) with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [ack_zero]
      omega
  · rw [ack_zero]
    omega

theorem le_scaledCost {c : Code} {k N n : ℕ} (hn : ack k N ≤ n) {b : ℕ}
    (hb : b ∈ scaledCost (c, k) n) : N ≤ b := by
  obtain ⟨s, hs, hb1⟩ := mem_scaledCost_eq.1 hb
  have hns : n < s := input_lt_of_mem_stepCount hs
  have h1 : ack k N ≤ s := by omega
  have h2 : N ≤ s := le_trans (le_of_lt (lt_ack_right k N)) h1
  have := Nat.le_findGreatest (P := fun y => ack k y ≤ s) h2 h1
  omega

/-- Along any program, the cost tends to infinity. -/
theorem scaledCost_unbounded (c : Code) (k N : ℕ) :
    ∃ N', ∀ n, N' ≤ n → ∀ b ∈ scaledCost (c, k) n, N ≤ b :=
  ⟨ack k N, fun _ hn _ hb => le_scaledCost hn hb⟩

/-! ## An arbitrarily hard decision problem

So that the main theorem is not about a trivially easy problem, we exhibit a decision problem
which is hard for the *standard* step-counting measure: for any primitive recursive bound `t`,
every algorithm for it exceeds `t` on infinitely many inputs. The problem diagonalises against
the code `c` with index `i` on the inputs `n` with `n.unpair.1 = i`. -/

/-- The code with index `i`. -/
def codeOf (i : ℕ) : Code := Denumerable.ofNat Code i

/-- A decision problem which no algorithm can solve within a primitive recursive time bound on
all but finitely many inputs. -/
def hardProblem (n : ℕ) : ℕ := 1 - ((evaln (ack n n) (codeOf n.unpair.1) n).getD 1)

theorem hardProblem_le_one (n : ℕ) : hardProblem n ≤ 1 := Nat.sub_le _ _

theorem computable_hardProblem : Computable hardProblem := by
  have h1 : Computable fun n : ℕ => ack n n := computable₂_ack.comp Computable.id Computable.id
  have h2 : Computable fun n : ℕ => codeOf n.unpair.1 :=
    (Computable.ofNat Code).comp (Computable.fst.comp Computable.unpair)
  have hp : Computable fun n : ℕ => ((ack n n, codeOf n.unpair.1), n) :=
    (h1.pair h2).pair Computable.id
  have h3 := primrec_evaln.to_comp.comp hp
  have h4 := Primrec.option_getD.to_comp.comp h3 (Computable.const 1)
  exact Primrec.nat_sub.to_comp.comp (Computable.const 1) h4

/-- Every algorithm for `hardProblem` needs more than `ack n n` steps for infinitely many `n`. -/
theorem hardProblem_hard {c : Code} (hc : eval c = fun n => Part.some (hardProblem n)) (N : ℕ) :
    ∃ n, N ≤ n ∧ ∀ s ∈ stepCount c n, ack n n < s := by
  refine ⟨Nat.pair (Encodable.encode c) N, Nat.right_le_pair _ _, ?_⟩
  intro s hs
  by_contra hle
  push_neg at hle
  set n := Nat.pair (Encodable.encode c) N with hn
  have hcode : codeOf n.unpair.1 = c := by
    simp [codeOf, hn, Denumerable.ofNat_encode]
  have hhalt : halts c n (ack n n) = true := halts_mono hle (mem_stepCount.1 hs).1
  obtain ⟨v, hv⟩ := halts_iff_exists.1 hhalt
  have hval : v = hardProblem n := by
    have hmem : v ∈ eval c n := evaln_sound hv
    rw [hc] at hmem
    simpa using hmem
  have hdef : hardProblem n = 1 - v := by
    have hev : evaln (ack n n) (codeOf n.unpair.1) n = some v := by rw [hcode]; exact hv
    rw [hardProblem, hev]
    rfl
  omega

/-- Every algorithm for `hardProblem` exceeds any prescribed primitive recursive time bound on
infinitely many inputs. -/
theorem hardProblem_hard_of_primrec (t : ℕ → ℕ) (ht : Nat.Primrec t) {c : Code}
    (hc : eval c = fun n => Part.some (hardProblem n)) (N : ℕ) :
    ∃ n, N ≤ n ∧ ∀ s ∈ stepCount c n, t n < s := by
  obtain ⟨m, hm⟩ := exists_lt_ack_of_nat_primrec ht
  obtain ⟨n, hn, h⟩ := hardProblem_hard hc (max N m)
  refine ⟨n, le_trans (le_max_left _ _) hn, fun s hs => ?_⟩
  have h1 := h s hs
  have h2 : ack m n ≤ ack n n := ack_mono_left n (le_trans (le_max_right _ _) hn)
  exact lt_of_lt_of_le (lt_of_lt_of_le (hm n) h2) (le_of_lt h1)

/-! ## The main theorem -/

/-- **Blum speedup**: there are problems with no fastest algorithm. -/
theorem blum_speedup :
    ∃ (M : BlumMeasure (Code × ℕ)) (f : ℕ → ℕ),
      Computable f ∧ (∀ n, f n ≤ 1) ∧
      (∃ p, M.sem p = fun n => Part.some (f n)) ∧
      M.NoFastestAlgorithm (fun n => Part.some (f n)) ∧
      ∀ t : ℕ → ℕ, Nat.Primrec t → ∀ c : Code, eval c = (fun n => Part.some (f n)) →
        ∀ N, ∃ n, N ≤ n ∧ ∀ s ∈ stepCount c n, t n < s := by
  refine ⟨blum, hardProblem, computable_hardProblem, hardProblem_le_one, ?_,
    blum_no_fastest _, fun t ht c hc N => hardProblem_hard_of_primrec t ht hc N⟩
  obtain ⟨c, hc⟩ := exists_code.1 (Partrec.nat_iff.1 computable_hardProblem.partrec)
  exact ⟨(c, 0), hc⟩

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

