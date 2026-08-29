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
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Disjointness Lb

Set disjointness on `n`-bit inputs has `Ω(n)` randomized communication
complexity: any public-coin randomized protocol which never accepts a pair of
intersecting sets, and accepts every pair of disjoint sets with probability at
least `1/2`, must communicate at least `n - 2` bits in the worst case.

The proof is the classical fooling-set argument combined with an averaging step
over the public coin:

* the `2 ^ n` pairs `(S, Sᶜ)` are all disjoint, hence each is accepted with
  probability at least `1/2`;
* averaging, some deterministic protocol in the support accepts at least
  `2 ^ n / 2` of them;
* by the rectangle property of protocols, two distinct such pairs cannot produce
  the same transcript (otherwise a mixed, intersecting pair `(S, Tᶜ)` would also
  be accepted, which is forbidden);
* a protocol of cost `c` has fewer than `2 ^ (c + 1)` transcripts, whence
  `2 ^ n / 2 ≤ 2 ^ (c + 1)`, i.e. `n ≤ c + 2`.

The randomized model formalized here is the one-sided error (public-coin) model:
errors are allowed only on disjoint pairs, and there the acceptance probability
need only exceed `1/2`.  The bound `n ≤ cost + 2` is tight up to an additive
constant, as witnessed by `CS.disjointness_ub`.
-/

namespace CS

/-! ## Deterministic communication protocols

A deterministic two-party protocol is a binary tree.  At an `alice` node the
first player sends one bit, computed from her input `x : X`; at a `bob` node the
second player sends one bit computed from his input `y : Y`.  A `leaf` carries
the output of the protocol.
-/

/-- A deterministic communication protocol tree for inputs `X` (Alice) and `Y` (Bob). -/
inductive Protocol (X Y : Type) : Type
  | leaf (b : Bool) : Protocol X Y
  | alice (f : X → Bool) (t0 t1 : Protocol X Y) : Protocol X Y
  | bob (g : Y → Bool) (t0 t1 : Protocol X Y) : Protocol X Y

namespace Protocol

variable {X Y : Type}

/-- The output of the protocol on the input pair `(x, y)`. -/
def run : Protocol X Y → X → Y → Bool
  | leaf b, _, _ => b
  | alice f t0 t1, x, y => if f x then run t1 x y else run t0 x y
  | bob g t0 t1, x, y => if g y then run t1 x y else run t0 x y

/-- The communication cost of a protocol: the number of bits exchanged in the
worst case, i.e. the depth of the protocol tree. -/
def cost : Protocol X Y → ℕ
  | leaf _ => 0
  | alice _ t0 t1 => 1 + max (cost t0) (cost t1)
  | bob _ t0 t1 => 1 + max (cost t0) (cost t1)

/-- A numerical encoding of the transcript (the sequence of bits exchanged) of
the protocol on the input pair `(x, y)`: the bits of the transcript preceded by
a leading `1`. -/
def code : Protocol X Y → X → Y → ℕ
  | leaf _, _, _ => 1
  | alice f t0 t1, x, y => if f x then 2 * code t1 x y + 1 else 2 * code t0 x y
  | bob g t0 t1, x, y => if g y then 2 * code t1 x y + 1 else 2 * code t0 x y

/-- A protocol of cost `c` has at most `2 ^ (c + 1)` possible transcripts. -/
theorem code_lt (P : Protocol X Y) : ∀ (x : X) (y : Y), code P x y < 2 ^ (P.cost + 1) := by
  induction P with
  | leaf b => intro x y; simp [code, cost]
  | alice f t0 t1 ih0 ih1 =>
      intro x y
      have h0 := ih0 x y
      have h1 := ih1 x y
      have e0 : (2:ℕ) ^ (cost t0 + 1) ≤ 2 ^ (max (cost t0) (cost t1) + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have e1 : (2:ℕ) ^ (cost t1 + 1) ≤ 2 ^ (max (cost t0) (cost t1) + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have e2 : (2:ℕ) ^ (1 + max (cost t0) (cost t1) + 1)
          = 2 * 2 ^ (max (cost t0) (cost t1) + 1) := by ring
      simp only [code, cost]
      split <;> omega
  | bob g t0 t1 ih0 ih1 =>
      intro x y
      have h0 := ih0 x y
      have h1 := ih1 x y
      have e0 : (2:ℕ) ^ (cost t0 + 1) ≤ 2 ^ (max (cost t0) (cost t1) + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have e1 : (2:ℕ) ^ (cost t1 + 1) ≤ 2 ^ (max (cost t0) (cost t1) + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have e2 : (2:ℕ) ^ (1 + max (cost t0) (cost t1) + 1)
          = 2 * 2 ^ (max (cost t0) (cost t1) + 1) := by ring
      simp only [code, cost]
      split <;> omega

/-- **Rectangle property** of protocols: if `(x, y)` and `(x', y')` produce the
same transcript, then so does the "mixed" pair `(x, y')`, and the protocol gives
it the same answer. -/
theorem rect (P : Protocol X Y) :
    ∀ (x x' : X) (y y' : Y), code P x y = code P x' y' →
      code P x y' = code P x y ∧ run P x y' = run P x y := by
  induction P with
  | leaf b => intro x x' y y' _; simp [code, run]
  | alice f t0 t1 ih0 ih1 =>
      intro x x' y y' h
      simp only [code, run] at h ⊢
      cases hx : f x
      · cases hx' : f x'
        · simp only [hx, hx', Bool.false_eq_true, if_false] at h ⊢
          obtain ⟨h1, h2⟩ := ih0 x x' y y' (by omega)
          exact ⟨by omega, h2⟩
        · simp only [hx, hx', Bool.false_eq_true, if_true, if_false] at h ⊢
          exact absurd h (by omega)
      · cases hx' : f x'
        · simp only [hx, hx', Bool.false_eq_true, if_true, if_false] at h ⊢
          exact absurd h (by omega)
        · simp only [hx, hx', if_true] at h ⊢
          obtain ⟨h1, h2⟩ := ih1 x x' y y' (by omega)
          exact ⟨by omega, h2⟩
  | bob g t0 t1 ih0 ih1 =>
      intro x x' y y' h
      simp only [code, run] at h ⊢
      cases hy : g y
      · cases hy' : g y'
        · simp only [hy, hy', Bool.false_eq_true, if_false] at h ⊢
          obtain ⟨h1, h2⟩ := ih0 x x' y y' (by omega)
          exact ⟨by omega, h2⟩
        · simp only [hy, hy', Bool.false_eq_true, if_true, if_false] at h ⊢
          exact absurd h (by omega)
      · cases hy' : g y'
        · simp only [hy, hy', Bool.false_eq_true, if_true, if_false] at h ⊢
          exact absurd h (by omega)
        · simp only [hy, hy', if_true] at h ⊢
          obtain ⟨h1, h2⟩ := ih1 x x' y y' (by omega)
          exact ⟨by omega, h2⟩

end Protocol

/-! ## Public-coin randomized protocols -/

/-- A public-coin randomized communication protocol: a finitely supported
probability distribution (with positive weights) over deterministic protocols. -/
structure RandProtocol (X Y : Type) (m : ℕ) where
  /-- The deterministic protocol used for each outcome of the public coin. -/
  proto : Fin m → Protocol X Y
  /-- The probability of each outcome of the public coin. -/
  weight : Fin m → ℝ
  /-- Outcomes of the coin all have positive probability. -/
  weight_pos : ∀ i, 0 < weight i
  /-- The weights form a probability distribution. -/
  weight_sum : ∑ i, weight i = 1

namespace RandProtocol

variable {X Y : Type} {m : ℕ}

/-- The (worst-case) communication cost of a randomized protocol. -/
noncomputable def cost (P : RandProtocol X Y m) : ℕ :=
  Finset.univ.sup fun i => (P.proto i).cost

/-- The probability that the randomized protocol outputs `true` on `(x, y)`. -/
noncomputable def acc (P : RandProtocol X Y m) (x : X) (y : Y) : ℝ :=
  ∑ i, if (P.proto i).run x y then P.weight i else 0

theorem cost_le (P : RandProtocol X Y m) (i : Fin m) : (P.proto i).cost ≤ P.cost :=
  Finset.le_sup (f := fun i => (P.proto i).cost) (Finset.mem_univ i)

/-- If the randomized protocol accepts `(x, y)` with probability `0`, then no
deterministic protocol in its support accepts `(x, y)`. -/
theorem run_false_of_acc_zero (P : RandProtocol X Y m) {x : X} {y : Y}
    (h : P.acc x y = 0) (i : Fin m) : (P.proto i).run x y = false := by
  by_contra hi
  have hi' : (P.proto i).run x y = true := by simpa using hi
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ (if (P.proto j).run x y then P.weight j else 0) := by
    intro j _
    by_cases hj : (P.proto j).run x y = true
    · rw [if_pos hj]; exact (P.weight_pos j).le
    · simp [hj]
  have hle : P.weight i ≤ P.acc x y := by
    have hsum := Finset.single_le_sum hnn (Finset.mem_univ i)
    rwa [if_pos hi'] at hsum
  rw [h] at hle
  exact absurd hle (not_le.2 (P.weight_pos i))

/-- The number of outcomes of the public coin is positive. -/
theorem pos_of_weights (P : RandProtocol X Y m) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have := P.weight_sum
    simp at this
  · exact hm

end RandProtocol

/-! ## Set disjointness -/

/-- Subsets of `Fin n` are encoded as Boolean vectors.  `Disj x y` says that the
sets encoded by `x` and `y` are disjoint. -/
def Disj {n : ℕ} (x y : Fin n → Bool) : Prop := ∀ i, x i = false ∨ y i = false

instance instDecidableDisj {n : ℕ} (x y : Fin n → Bool) : Decidable (Disj x y) := by
  unfold Disj; infer_instance

/-- A set and its complement are disjoint: these are the fooling pairs. -/
theorem disj_self_compl {n : ℕ} (S : Fin n → Bool) : Disj S (fun i => !S i) := by
  intro i; cases h : S i <;> simp [h]

/-- If `S j = true` and `T j = false` then `S` meets the complement of `T`. -/
theorem not_disj_of_ne {n : ℕ} {S T : Fin n → Bool} (j : Fin n) (hS : S j = true)
    (hT : T j = false) : ¬ Disj S (fun i => !T i) := by
  intro h
  rcases h j with h | h
  · rw [hS] at h; exact Bool.noConfusion h
  · simp only [hT] at h; exact Bool.noConfusion h

/-! ## The lower bound -/

/-- The fooling-set injection: for a protocol that never accepts an intersecting
pair, distinct accepted fooling pairs have distinct transcripts. -/
theorem fooling_injOn {n m : ℕ} (P : RandProtocol (Fin n → Bool) (Fin n → Bool) m)
    (hsound : ∀ x y, ¬ Disj x y → P.acc x y = 0) (i : Fin m) :
    Set.InjOn (fun S : Fin n → Bool => (P.proto i).code S (fun j => !S j))
      ↑((Finset.univ : Finset (Fin n → Bool)).filter
        fun S => (P.proto i).run S (fun j => !S j) = true) := by
  intro S hS T hT hcode
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hS hT
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, S j ≠ T j := by
    by_contra hall
    exact hne (funext fun j => by simpa using not_exists.1 hall j)
  -- in either case a mixed, intersecting pair is accepted by `P.proto i`
  have main : ∀ (A B : Fin n → Bool), A j = true → B j = false →
      (P.proto i).code A (fun k => !A k) = (P.proto i).code B (fun k => !B k) →
      (P.proto i).run A (fun k => !A k) = true → False := by
    intro A B hA hB hcode' hrun
    obtain ⟨-, h2⟩ := (P.proto i).rect A B (fun k => !A k) (fun k => !B k) hcode'
    have hacc : P.acc A (fun k => !B k) = 0 := hsound _ _ (not_disj_of_ne j hA hB)
    have := P.run_false_of_acc_zero hacc i
    rw [this, hrun] at h2
    exact Bool.noConfusion h2
  cases hSj : S j with
  | false =>
      have hTj : T j = true := by
        cases hTj' : T j
        · exact absurd (hSj.trans hTj'.symm) hj
        · rfl
      exact main T S hTj hSj hcode.symm hT
  | true =>
      have hTj : T j = false := by
        cases hTj' : T j
        · rfl
        · exact absurd (hSj.trans hTj'.symm) hj
      exact main S T hSj hTj hcode hS

/-- **Set disjointness has `Ω(n)` randomized communication complexity.**

Any public-coin randomized protocol `P` that

* never accepts a pair of intersecting sets (`hsound`), and
* accepts every pair of disjoint sets with probability at least `1/2` (`hcomp`),

must exchange at least `n - 2` bits in the worst case. -/
theorem disjointness_lb {n m : ℕ} (P : RandProtocol (Fin n → Bool) (Fin n → Bool) m)
    (hsound : ∀ x y, ¬ Disj x y → P.acc x y = 0)
    (hcomp : ∀ x y, Disj x y → 1 / 2 ≤ P.acc x y) :
    n ≤ P.cost + 2 := by
  classical
  set A : Fin m → ℝ := fun i =>
    (((Finset.univ : Finset (Fin n → Bool)).filter
      fun S => (P.proto i).run S (fun j => !S j) = true).card : ℝ) with hA
  -- Step 1: the total acceptance probability over the fooling set is at least `2 ^ n / 2`.
  have hcard : ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) = 2 ^ n := by
    simp
  have hlow : (2:ℝ) ^ n / 2 ≤ ∑ S : Fin n → Bool, P.acc S (fun j => !S j) := by
    have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → Bool)))
      (f := fun _ : Fin n → Bool => (1:ℝ) / 2)
      (g := fun S : Fin n → Bool => P.acc S (fun j => !S j))
      (fun S _ => hcomp _ _ (disj_self_compl S))
    simpa [hcard, div_eq_mul_inv, mul_comm] using this
  -- Step 2: rewrite that total as a weighted average of the counts `A i`.
  have hswap : ∑ S : Fin n → Bool, P.acc S (fun j => !S j) = ∑ i, P.weight i * A i := by
    simp only [RandProtocol.acc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hA, mul_comm]
  -- Step 3: some deterministic protocol in the support accepts many fooling pairs.
  have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, P.pos_of_weights⟩, Finset.mem_univ _⟩
  have hex : ∃ i, (2:ℝ) ^ n / 2 ≤ A i := by
    by_contra hall
    push_neg at hall
    have hlt : ∑ i, P.weight i * A i < ∑ i, P.weight i * ((2:ℝ) ^ n / 2) := by
      refine Finset.sum_lt_sum_of_nonempty hne fun i _ => ?_
      exact mul_lt_mul_of_pos_left (hall i) (P.weight_pos i)
    rw [← Finset.sum_mul, P.weight_sum, one_mul] at hlt
    rw [hswap] at hlow
    linarith
  obtain ⟨i, hi⟩ := hex
  -- Step 4: the accepted fooling pairs inject into the set of transcripts.
  have hcardle :
      ((Finset.univ : Finset (Fin n → Bool)).filter
        fun S => (P.proto i).run S (fun j => !S j) = true).card
        ≤ (Finset.range (2 ^ ((P.proto i).cost + 1))).card := by
    refine Finset.card_le_card_of_injOn
      (fun S => (P.proto i).code S (fun j => !S j)) (fun S _ => ?_)
      (fooling_injOn P hsound i)
    exact Finset.mem_range.2 ((P.proto i).code_lt _ _)
  rw [Finset.card_range] at hcardle
  have hcardle' : A i ≤ (2:ℝ) ^ ((P.proto i).cost + 1) := by
    have hcast : (((Finset.univ : Finset (Fin n → Bool)).filter
        fun S => (P.proto i).run S (fun j => !S j) = true).card : ℝ)
        ≤ ((2 ^ ((P.proto i).cost + 1) : ℕ) : ℝ) := Nat.cast_le.2 hcardle
    simpa [hA] using hcast
  have hstep : (2:ℝ) ^ n / 2 ≤ (2:ℝ) ^ (P.cost + 1) := by
    refine hi.trans (hcardle'.trans ?_)
    exact pow_le_pow_right₀ (by norm_num) (by have := P.cost_le i; omega)
  have hfin : (2:ℝ) ^ n ≤ (2:ℝ) ^ (P.cost + 2) := by
    have : (2:ℝ) ^ (P.cost + 2) = 2 * 2 ^ (P.cost + 1) := by ring
    linarith
  have : (2:ℕ) ^ n ≤ 2 ^ (P.cost + 2) := by exact_mod_cast hfin
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

/-! ## The bound is not vacuous: a matching protocol

Alice sends her whole input, then Bob announces the answer.  This is a
(deterministic, hence randomized) protocol of cost `n + 1` satisfying both
hypotheses of `CS.disjointness_lb`, so the hypotheses are satisfiable and the
lower bound `n - 2` is tight up to an additive constant. -/

/-- Alice reveals the coordinates in `l`, keeping the partial guess `xg`; then
Bob announces whether the two sets are disjoint. -/
def revealProtocol {n : ℕ} :
    List (Fin n) → (Fin n → Bool) → Protocol (Fin n → Bool) (Fin n → Bool)
  | [], xg => Protocol.bob (fun y => decide (Disj xg y)) (Protocol.leaf false) (Protocol.leaf true)
  | j :: l, xg =>
      Protocol.alice (fun x => x j)
        (revealProtocol l (Function.update xg j false))
        (revealProtocol l (Function.update xg j true))

theorem cost_revealProtocol {n : ℕ} :
    ∀ (l : List (Fin n)) (xg : Fin n → Bool), (revealProtocol l xg).cost = l.length + 1 := by
  intro l
  induction l with
  | nil => intro xg; simp [revealProtocol, Protocol.cost]
  | cons j l ih =>
      intro xg
      simp [revealProtocol, Protocol.cost, ih]
      omega

theorem run_revealProtocol {n : ℕ} :
    ∀ (l : List (Fin n)) (xg x y : Fin n → Bool), (∀ j, j ∉ l → xg j = x j) →
      (revealProtocol l xg).run x y = decide (Disj x y) := by
  intro l
  induction l with
  | nil =>
      intro xg x y h
      have hx : xg = x := funext fun j => h j (by simp)
      subst hx
      simp [revealProtocol, Protocol.run]
  | cons j l ih =>
      intro xg x y h
      have hupd : ∀ k, k ∉ l → Function.update xg j (x j) k = x k := by
        intro k hk
        by_cases hkj : k = j
        · subst hkj; simp
        · rw [Function.update_of_ne hkj]
          exact h k (by simp [hkj, hk])
      cases hxj : x j
      · have := ih (Function.update xg j false) x y (by simpa [hxj] using hupd)
        simp [revealProtocol, Protocol.run, hxj, this]
      · have := ih (Function.update xg j true) x y (by simpa [hxj] using hupd)
        simp [revealProtocol, Protocol.run, hxj, this]

/-- The hypotheses of `CS.disjointness_lb` are satisfiable: there is a protocol
of cost `n + 1` which computes disjointness exactly. -/
theorem disjointness_ub (n : ℕ) :
    ∃ P : RandProtocol (Fin n → Bool) (Fin n → Bool) 1,
      (∀ x y, ¬ Disj x y → P.acc x y = 0) ∧ (∀ x y, Disj x y → 1 / 2 ≤ P.acc x y) ∧
        P.cost = n + 1 := by
  classical
  refine ⟨{ proto := fun _ => revealProtocol (List.finRange n) (fun _ => false)
            weight := fun _ => 1
            weight_pos := fun _ => one_pos
            weight_sum := by simp }, ?_, ?_, ?_⟩
  · intro x y hxy
    have hrun : (revealProtocol (List.finRange n) (fun _ => false)).run x y = decide (Disj x y) :=
      run_revealProtocol _ _ x y (by intro j hj; exact absurd (List.mem_finRange j) hj)
    simp [RandProtocol.acc, hrun, hxy]
  · intro x y hxy
    have hrun : (revealProtocol (List.finRange n) (fun _ => false)).run x y = decide (Disj x y) :=
      run_revealProtocol _ _ x y (by intro j hj; exact absurd (List.mem_finRange j) hj)
    simp [RandProtocol.acc, hrun, hxy]
    norm_num
  · simp [RandProtocol.cost, cost_revealProtocol]

end CS

