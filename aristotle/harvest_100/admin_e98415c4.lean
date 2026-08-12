/-
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.PermanentGadget

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope of the formalization

The statement "the `0/1` permanent is `#P`-complete" has two halves.  What is formalized here is

* the *membership* half, in full: the `0/1` permanent is the counting function of an explicitly
  constructed family of Boolean verifier circuits of polynomial size (`InSharpP perm01Count`);
* the combinatorial identity underlying the problem: the permanent of a `0/1` matrix is the
  number of perfect matchings of the associated bipartite graph;
* the weight-elimination step of Valiant's hardness argument: restricting to `0/1` entries loses
  no generality, since every matrix of natural numbers has the same permanent as a `0/1` matrix
  of controlled size.

The remaining half of Valiant's theorem, namely the parsimonious reduction of an arbitrary `#P`
verifier to a permanent (the gadget construction), is *not* formalized here.
-/

set_option autoImplicit false

namespace CS

/-! ## Boolean circuits -/

/-- Boolean circuits (formulas) over a set `ι` of input variables. -/
inductive Circuit (ι : Type) where
  | var : ι → Circuit ι
  | const : Bool → Circuit ι
  | not : Circuit ι → Circuit ι
  | and : Circuit ι → Circuit ι → Circuit ι
  | or : Circuit ι → Circuit ι → Circuit ι

namespace Circuit

variable {ι : Type}

/-- Evaluation of a circuit at a Boolean assignment of its variables. -/
def eval : Circuit ι → (ι → Bool) → Bool
  | var i, f => f i
  | const b, _ => b
  | not c, f => !c.eval f
  | and c d, f => c.eval f && d.eval f
  | or c d, f => c.eval f || d.eval f

/-- The size (number of gates) of a circuit. -/
def size : Circuit ι → ℕ
  | var _ => 1
  | const _ => 1
  | not c => 1 + c.size
  | and c d => 1 + c.size + d.size
  | or c d => 1 + c.size + d.size

/-- Conjunction of a list of circuits. -/
def allL : List (Circuit ι) → Circuit ι
  | [] => const true
  | c :: cs => and c (allL cs)

/-- Disjunction of a list of circuits. -/
def anyL : List (Circuit ι) → Circuit ι
  | [] => const false
  | c :: cs => or c (anyL cs)

@[simp] theorem eval_allL (l : List (Circuit ι)) (f : ι → Bool) :
    (allL l).eval f = true ↔ ∀ c ∈ l, c.eval f = true := by
  induction l with
  | nil => simp [allL, eval]
  | cons c cs ih => simp [allL, eval, ih]

@[simp] theorem eval_anyL (l : List (Circuit ι)) (f : ι → Bool) :
    (anyL l).eval f = true ↔ ∃ c ∈ l, c.eval f = true := by
  induction l with
  | nil => simp [anyL, eval]
  | cons c cs ih => simp [anyL, eval, ih]

theorem size_allL_le (l : List (Circuit ι)) (s : ℕ) (h : ∀ c ∈ l, c.size ≤ s) :
    (allL l).size ≤ 1 + l.length * (1 + s) := by
  induction l with
  | nil => simp [allL, size]
  | cons c cs ih =>
      have hc : c.size ≤ s := h c (by simp)
      have := ih (fun d hd => h d (by simp [hd]))
      simp only [allL, size, List.length_cons, Nat.succ_mul]
      omega

theorem size_anyL_le (l : List (Circuit ι)) (s : ℕ) (h : ∀ c ∈ l, c.size ≤ s) :
    (anyL l).size ≤ 1 + l.length * (1 + s) := by
  induction l with
  | nil => simp [anyL, size]
  | cons c cs ih =>
      have hc : c.size ≤ s := h c (by simp)
      have := ih (fun d hd => h d (by simp [hd]))
      simp only [anyL, size, List.length_cons, Nat.succ_mul]
      omega

end Circuit

/-! ## A non-uniform version of the counting class `#P`

A family of counting functions `f n : (ι n → Bool) → ℕ` belongs to `InSharpP` if there is a
family of polynomial-size Boolean verifier circuits `C n`, taking the input bits together with
polynomially many witness bits, such that `f n x` is exactly the number of witnesses accepted
by `C n` on input `x`.  This is the standard witness-counting description of `#P`, with
"polynomial-time verifier" modelled by "polynomial-size Boolean circuit" (i.e. the
non-uniform class `#P/poly`). -/
def InSharpP {ι : ℕ → Type} (f : ∀ n, (ι n → Bool) → ℕ) : Prop :=
  ∃ (ω : ℕ → Type) (C : ∀ n, Circuit (ι n ⊕ ω n)) (c k : ℕ),
    (∀ n, Finite (ω n)) ∧
    (∀ n, Nat.card (ω n) ≤ c * (n + 1) ^ k) ∧
    (∀ n, (C n).size ≤ c * (n + 1) ^ k) ∧
    (∀ n x, f n x = Nat.card {w : ω n → Bool // (C n).eval (Sum.elim x w) = true})

/-! ## The `0/1` permanent as a counting function -/

/-- The `0/1` matrix described by a bit vector indexed by pairs. -/
def mat01 (n : ℕ) (x : Fin n × Fin n → Bool) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => if x (i, j) then 1 else 0

/-- The permanent of a `0/1` matrix, as a counting function of the matrix' bits. -/
def perm01Count (n : ℕ) (x : Fin n × Fin n → Bool) : ℕ := (mat01 n x).permanent

/-- The permanent of a `0/1` matrix counts the perfect matchings of the associated bipartite
graph, i.e. the permutations `σ` with all entries `M (σ i) i` equal to `1`. -/
theorem perm01Count_eq_card_perm (n : ℕ) (x : Fin n × Fin n → Bool) :
    perm01Count n x = Nat.card {σ : Equiv.Perm (Fin n) // ∀ i, x (σ i, i) = true} := by
  classical
  have h1 : perm01Count n x
      = ∑ σ : Equiv.Perm (Fin n), if (∀ i, x (σ i, i) = true) then 1 else 0 := by
    unfold perm01Count Matrix.permanent
    refine Finset.sum_congr rfl ?_
    intro σ _
    by_cases h : ∀ i, x (σ i, i) = true
    · simp [mat01, h]
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      rw [if_neg (by push_neg; exact ⟨i, hi⟩)]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [mat01, hi])
  rw [h1, Finset.sum_boole]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

/-! ## The verifier circuit for the permanent -/

/-- Variables of the verifier circuit: the `n²` input bits and the `n²` witness bits. -/
abbrev PermVar (n : ℕ) : Type := (Fin n × Fin n) ⊕ (Fin n × Fin n)

/-- The circuit variable holding the input bit `(i, j)`. -/
def xv (n : ℕ) (i j : Fin n) : Circuit (PermVar n) := .var (.inl (i, j))

/-- The circuit variable holding the witness bit `(i, j)`. -/
def wv (n : ℕ) (i j : Fin n) : Circuit (PermVar n) := .var (.inr (i, j))

/-- "The `j`-th column of the witness contains exactly one `1`." -/
def colExactlyOne (n : ℕ) (j : Fin n) : Circuit (PermVar n) :=
  .anyL ((List.finRange n).map fun i =>
    .and (wv n i j)
      (.allL ((List.finRange n).map fun i' =>
        if i' = i then .const true else .not (wv n i' j))))

/-- "The `i`-th row of the witness contains exactly one `1`." -/
def rowExactlyOne (n : ℕ) (i : Fin n) : Circuit (PermVar n) :=
  .anyL ((List.finRange n).map fun j =>
    .and (wv n i j)
      (.allL ((List.finRange n).map fun j' =>
        if j' = j then .const true else .not (wv n i j'))))

/-- "Every `1` of the witness sits at a position where the input matrix has a `1`." -/
def dominated (n : ℕ) : Circuit (PermVar n) :=
  .allL ((List.finRange n).flatMap fun i =>
    (List.finRange n).map fun j => .or (.not (wv n i j)) (xv n i j))

/-- The verifier circuit for the `0/1` permanent: it accepts a witness iff the witness is a
permutation matrix dominated by the input matrix. -/
def permVerifier (n : ℕ) : Circuit (PermVar n) :=
  .allL [.allL ((List.finRange n).map (rowExactlyOne n)),
         .allL ((List.finRange n).map (colExactlyOne n)),
         dominated n]

theorem eval_rowExactlyOne (n : ℕ) (i : Fin n) (x w : Fin n × Fin n → Bool) :
    (rowExactlyOne n i).eval (Sum.elim x w) = true ↔ ∃! j, w (i, j) = true := by
  simp only [rowExactlyOne, Circuit.eval_anyL, List.mem_map,
    List.mem_finRange, true_and]
  constructor
  · rintro ⟨c, ⟨j, rfl⟩, hc⟩
    simp only [Circuit.eval, wv, Sum.elim_inr, Bool.and_eq_true] at hc
    refine ⟨j, hc.1, ?_⟩
    intro j' hj'
    by_contra hne
    have := hc.2
    simp only [Circuit.eval_allL, List.mem_map, List.mem_finRange, true_and] at this
    have h2 := this _ ⟨j', rfl⟩
    rw [if_neg hne] at h2
    simp [Circuit.eval, hj'] at h2
  · rintro ⟨j, hj, huniq⟩
    refine ⟨_, ⟨j, rfl⟩, ?_⟩
    simp only [Circuit.eval, wv, Sum.elim_inr, Bool.and_eq_true]
    refine ⟨hj, ?_⟩
    simp only [Circuit.eval_allL, List.mem_map, List.mem_finRange, true_and]
    rintro c ⟨j', rfl⟩
    by_cases hj' : j' = j
    · simp [hj', Circuit.eval]
    · rw [if_neg hj']
      simp only [Circuit.eval, Sum.elim_inr, Bool.not_eq_true']
      by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      exact hj' (huniq j' hcon)

theorem eval_colExactlyOne (n : ℕ) (j : Fin n) (x w : Fin n × Fin n → Bool) :
    (colExactlyOne n j).eval (Sum.elim x w) = true ↔ ∃! i, w (i, j) = true := by
  simp only [colExactlyOne, Circuit.eval_anyL, List.mem_map,
    List.mem_finRange, true_and]
  constructor
  · rintro ⟨c, ⟨i, rfl⟩, hc⟩
    simp only [Circuit.eval, wv, Sum.elim_inr, Bool.and_eq_true] at hc
    refine ⟨i, hc.1, ?_⟩
    intro i' hi'
    by_contra hne
    have := hc.2
    simp only [Circuit.eval_allL, List.mem_map, List.mem_finRange, true_and] at this
    have h2 := this _ ⟨i', rfl⟩
    rw [if_neg hne] at h2
    simp [Circuit.eval, hi'] at h2
  · rintro ⟨i, hi, huniq⟩
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simp only [Circuit.eval, wv, Sum.elim_inr, Bool.and_eq_true]
    refine ⟨hi, ?_⟩
    simp only [Circuit.eval_allL, List.mem_map, List.mem_finRange, true_and]
    rintro c ⟨i', rfl⟩
    by_cases hi' : i' = i
    · simp [hi', Circuit.eval]
    · rw [if_neg hi']
      simp only [Circuit.eval, Sum.elim_inr, Bool.not_eq_true']
      by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      exact hi' (huniq i' hcon)

theorem eval_dominated (n : ℕ) (x w : Fin n × Fin n → Bool) :
    (dominated n).eval (Sum.elim x w) = true ↔ ∀ i j, w (i, j) = true → x (i, j) = true := by
  simp only [dominated, Circuit.eval_allL, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and]
  constructor
  · rintro h i j hw
    have := h _ ⟨i, ⟨j, rfl⟩⟩
    simp only [Circuit.eval, wv, xv, Sum.elim_inr, Sum.elim_inl, hw] at this
    simpa using this
  · rintro h c ⟨i, ⟨j, rfl⟩⟩
    simp only [Circuit.eval, wv, xv, Sum.elim_inr, Sum.elim_inl]
    cases hw : w (i, j) with
    | false => simp
    | true => simp [h i j hw]

theorem eval_permVerifier (n : ℕ) (x w : Fin n × Fin n → Bool) :
    (permVerifier n).eval (Sum.elim x w) = true ↔
      ((∀ i, ∃! j, w (i, j) = true) ∧ (∀ j, ∃! i, w (i, j) = true) ∧
        ∀ i j, w (i, j) = true → x (i, j) = true) := by
  simp only [permVerifier, Circuit.eval_allL, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun j => ?_, ?_⟩
    · have := h _ (Or.inl rfl)
      rw [Circuit.eval_allL] at this
      exact (eval_rowExactlyOne n i x w).1
        (this _ (List.mem_map_of_mem (List.mem_finRange i)))
    · have := h _ (Or.inr (Or.inl rfl))
      rw [Circuit.eval_allL] at this
      exact (eval_colExactlyOne n j x w).1
        (this _ (List.mem_map_of_mem (List.mem_finRange j)))
    · exact (eval_dominated n x w).1 (h _ (Or.inr (Or.inr rfl)))
  · rintro ⟨hr, hc, hd⟩ c hcm
    rcases hcm with rfl | rfl | rfl
    · rw [Circuit.eval_allL]
      intro d hd
      rw [List.mem_map] at hd
      obtain ⟨i, -, rfl⟩ := hd
      exact (eval_rowExactlyOne n i x w).2 (hr i)
    · rw [Circuit.eval_allL]
      intro d hd
      rw [List.mem_map] at hd
      obtain ⟨j, -, rfl⟩ := hd
      exact (eval_colExactlyOne n j x w).2 (hc j)
    · exact (eval_dominated n x w).2 hd

/-! ## Counting the accepted witnesses -/

theorem card_witnesses (n : ℕ) (x : Fin n × Fin n → Bool) :
    Nat.card {w : Fin n × Fin n → Bool // (permVerifier n).eval (Sum.elim x w) = true}
      = Nat.card {σ : Equiv.Perm (Fin n) // ∀ i, x (σ i, i) = true} := by
  classical
  refine (Nat.card_eq_of_bijective
    (fun (σ : {σ : Equiv.Perm (Fin n) // ∀ i, x (σ i, i) = true}) =>
      (⟨fun p => decide (σ.1 p.2 = p.1), ?_⟩ :
        {w : Fin n × Fin n → Bool // (permVerifier n).eval (Sum.elim x w) = true})) ?_).symm
  · rw [eval_permVerifier]
    refine ⟨fun i => ⟨σ.1.symm i, by simp, ?_⟩, fun j => ⟨σ.1 j, by simp, ?_⟩, ?_⟩
    · intro j hj
      simp only [decide_eq_true_eq] at hj
      simp [← hj]
    · intro i hi
      simp only [decide_eq_true_eq] at hi
      exact hi.symm
    · intro i j hij
      simp only [decide_eq_true_eq] at hij
      subst hij
      exact σ.2 j
  · constructor
    · rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
      simp only [Subtype.mk.injEq] at h
      ext j
      have hj : τ j = σ j := by simpa using congrFun h (σ j, j)
      exact congrArg Fin.val hj.symm
    · rintro ⟨w, hw⟩
      rw [eval_permVerifier] at hw
      obtain ⟨hrow, hcol, hdom⟩ := hw
      choose g hg huniq using hcol
      have hginj : Function.Injective g := by
        intro j j' hjj
        obtain ⟨jj, _, hu⟩ := hrow (g j)
        have h1 : w (g j, j) = true := hg j
        have h2 : w (g j, j') = true := by rw [hjj]; exact hg j'
        rw [hu j h1, hu j' h2]
      have hgbij : Function.Bijective g := Finite.injective_iff_bijective.1 hginj
      refine ⟨⟨Equiv.ofBijective g hgbij, fun i => hdom _ _ (hg i)⟩, ?_⟩
      apply Subtype.ext
      funext p
      obtain ⟨i, j⟩ := p
      simp only [Equiv.ofBijective_apply]
      cases hwij : w (i, j) with
      | true => simp [huniq j i hwij]
      | false =>
          have : g j ≠ i := by
            intro h
            rw [← h] at hwij
            rw [hg j] at hwij
            exact Bool.noConfusion hwij
          simp [this]

/-! ## Size of the verifier circuit -/

theorem size_wv (n : ℕ) (i j : Fin n) : (wv n i j).size = 1 := rfl

theorem size_rowExactlyOne (n : ℕ) (i : Fin n) :
    (rowExactlyOne n i).size ≤ 1 + n * (5 + 3 * n) := by
  have hinner : ∀ j : Fin n,
      (Circuit.allL ((List.finRange n).map fun j' =>
        if j' = j then Circuit.const true else Circuit.not (wv n i j'))).size
        ≤ 1 + n * 3 := by
    intro j
    have := Circuit.size_allL_le
      ((List.finRange n).map fun j' =>
        if j' = j then Circuit.const true else Circuit.not (wv n i j')) 2 ?_
    · simpa using this
    · rintro c hc
      simp only [List.mem_map, List.mem_finRange, true_and] at hc
      obtain ⟨j', rfl⟩ := hc
      by_cases h : j' = j <;> simp [h, Circuit.size, wv]
  refine le_trans (Circuit.size_anyL_le _ (4 + 3 * n) ?_) ?_
  · rintro c hc
    simp only [List.mem_map, List.mem_finRange, true_and] at hc
    obtain ⟨j, rfl⟩ := hc
    have := hinner j
    simp only [Circuit.size, size_wv]
    omega
  · simp only [List.length_map, List.length_finRange]
    have h5 : 1 + (4 + 3 * n) = 5 + 3 * n := by omega
    rw [h5]

theorem size_colExactlyOne (n : ℕ) (j : Fin n) :
    (colExactlyOne n j).size ≤ 1 + n * (5 + 3 * n) := by
  have hinner : ∀ i : Fin n,
      (Circuit.allL ((List.finRange n).map fun i' =>
        if i' = i then Circuit.const true else Circuit.not (wv n i' j))).size
        ≤ 1 + n * 3 := by
    intro i
    have := Circuit.size_allL_le
      ((List.finRange n).map fun i' =>
        if i' = i then Circuit.const true else Circuit.not (wv n i' j)) 2 ?_
    · simpa using this
    · rintro c hc
      simp only [List.mem_map, List.mem_finRange, true_and] at hc
      obtain ⟨i', rfl⟩ := hc
      by_cases h : i' = i <;> simp [h, Circuit.size, wv]
  refine le_trans (Circuit.size_anyL_le _ (4 + 3 * n) ?_) ?_
  · rintro c hc
    simp only [List.mem_map, List.mem_finRange, true_and] at hc
    obtain ⟨i, rfl⟩ := hc
    have := hinner i
    simp only [Circuit.size, size_wv]
    omega
  · simp only [List.length_map, List.length_finRange]
    have h5 : 1 + (4 + 3 * n) = 5 + 3 * n := by omega
    rw [h5]

theorem size_dominated (n : ℕ) : (dominated n).size ≤ 1 + n * n * 6 := by
  refine le_trans (Circuit.size_allL_le _ 5 ?_) ?_
  · rintro c hc
    simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hc
    obtain ⟨i, j, rfl⟩ := hc
    simp [Circuit.size, wv, xv]
  · simp [List.length_flatMap]

theorem size_permVerifier (n : ℕ) : (permVerifier n).size ≤ 100 * (n + 1) ^ 3 := by
  have h1 : (Circuit.allL ((List.finRange n).map (rowExactlyOne n))).size
      ≤ 1 + n * (1 + (1 + n * (5 + 3 * n))) := by
    refine le_trans (Circuit.size_allL_le _ (1 + n * (5 + 3 * n)) ?_) ?_
    · rintro c hc
      simp only [List.mem_map, List.mem_finRange, true_and] at hc
      obtain ⟨i, rfl⟩ := hc
      exact size_rowExactlyOne n i
    · simp
  have h2 : (Circuit.allL ((List.finRange n).map (colExactlyOne n))).size
      ≤ 1 + n * (1 + (1 + n * (5 + 3 * n))) := by
    refine le_trans (Circuit.size_allL_le _ (1 + n * (5 + 3 * n)) ?_) ?_
    · rintro c hc
      simp only [List.mem_map, List.mem_finRange, true_and] at hc
      obtain ⟨j, rfl⟩ := hc
      exact size_colExactlyOne n j
    · simp
  have h3 := size_dominated n
  have hexp : (permVerifier n).size
      = 1 + (Circuit.allL ((List.finRange n).map (rowExactlyOne n))).size
          + (1 + (Circuit.allL ((List.finRange n).map (colExactlyOne n))).size
            + (1 + (dominated n).size + 1)) := by
    simp [permVerifier, Circuit.allL, Circuit.size]
  rw [hexp]
  have hcube : 100 * (n + 1) ^ 3 = 100 * (n ^ 3 + 3 * n ^ 2 + 3 * n + 1) := by ring
  rw [hcube]
  nlinarith [sq_nonneg n, Nat.zero_le n]

/-! ## Main theorem -/

/--
**Valiant's permanent, formalized content.**

Three statements about the `0/1` permanent:

1. it lies in (the non-uniform version of) `#P`: it is the number of witnesses accepted by an
   explicitly constructed family of Boolean verifier circuits of polynomial size;
2. it counts perfect matchings: the permanent of a `0/1` matrix is the number of permutations
   `σ` with `x (σ i, i)` for all `i`;
3. weight elimination: every matrix with natural number entries has the same permanent as a
   `0/1` matrix of controlled size, so the `0/1` case is no easier than the weighted case.

The gadget reduction showing `#P`-hardness of the permanent is not part of this formalization;
see the module docstring.
-/
theorem valiant_permanent :
    InSharpP perm01Count ∧
      (∀ (n : ℕ) (x : Fin n × Fin n → Bool),
        perm01Count n x = Nat.card {σ : Equiv.Perm (Fin n) // ∀ i, x (σ i, i) = true}) ∧
      (∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℕ),
        ∃ (N : ℕ) (B : Matrix (Fin N) (Fin N) ℕ),
          N ≤ m + excess A ∧ (∀ i j, B i j ≤ 1) ∧ B.permanent = A.permanent) := by
  refine ⟨⟨fun n => Fin n × Fin n, permVerifier, 100, 3, fun n => inferInstance, ?_, ?_, ?_⟩,
    perm01Count_eq_card_perm, ?_⟩
  · intro n
    simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin]
    nlinarith [Nat.zero_le n]
  · exact size_permVerifier
  · intro n x
    rw [perm01Count_eq_card_perm, card_witnesses]
  · intro m A
    simpa using exists_01_permanent A

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

import Mathlib

/-!
# Weight elimination for the permanent

This file contains the "weight simulation" step of Valiant's argument: the permanent of an
arbitrary matrix with natural number entries is equal to the permanent of a `0/1` matrix of
controlled size.  Consequently, computing the permanent of `0/1` matrices is at least as hard
as computing the permanent of matrices with (unary encoded) nonnegative integer weights.

The construction replaces one unit of a weight `A r c ≥ 2` by an extra row and column: this is
the standard "parallel edge" gadget, expressed at the level of matrices.
-/

set_option autoImplicit false

namespace CS

open Finset Equiv

variable {α β : Type} [Fintype α] [DecidableEq α]

/-- Reindexing a matrix by an equivalence does not change its permanent. -/
theorem permanent_submatrix_equiv [Fintype β] [DecidableEq β] (e : β ≃ α) (M : Matrix α α ℕ) :
    (M.submatrix e e).permanent = M.permanent := by
  rw [Matrix.permanent, Matrix.permanent, ← Equiv.sum_comp (Equiv.permCongr e)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  refine Fintype.prod_equiv e (fun i : β => (M.submatrix e e) (σ i) i)
    (fun k : α => M ((Equiv.permCongr e σ) k) k) fun i => ?_
  simp [Matrix.submatrix, Equiv.permCongr]

/-- The matrix `M` with the entry at position `(r, c)` replaced by `v`. -/
def setEntry (M : Matrix α α ℕ) (r c : α) (v : ℕ) : Matrix α α ℕ :=
  fun i j => if i = r ∧ j = c then v else M i j

omit [Fintype α] in
@[simp] theorem setEntry_self (M : Matrix α α ℕ) (r c : α) (v : ℕ) : setEntry M r c v r c = v := by
  simp [setEntry]

omit [Fintype α] in
theorem setEntry_of_ne (M : Matrix α α ℕ) (r c : α) (v : ℕ) {i j : α} (h : ¬(i = r ∧ j = c)) :
    setEntry M r c v i j = M i j := by simp [setEntry, h]

omit [Fintype α] in
theorem setEntry_eq_self (M : Matrix α α ℕ) (r c : α) : setEntry M r c (M r c) = M := by
  funext i j
  by_cases h : i = r ∧ j = c
  · obtain ⟨rfl, rfl⟩ := h; simp
  · exact setEntry_of_ne M r c _ h

/-- The sum, over the permutations sending `c` to `r`, of the products of the remaining entries;
this is the permanent of the minor obtained by deleting row `r` and column `c`. -/
def minorSum (M : Matrix α α ℕ) (r c : α) : ℕ :=
  ∑ e ∈ univ.filter (fun e : Equiv.Perm α => e c = r), ∏ j ∈ univ.erase c, M (e j) j

/-- The contribution to the permanent of the permutations *not* sending `c` to `r`. -/
def restSum (M : Matrix α α ℕ) (r c : α) : ℕ :=
  ∑ e ∈ univ.filter (fun e : Equiv.Perm α => ¬ e c = r), ∏ j, M (e j) j

/-- The permanent is affine in each entry. -/
theorem permanent_setEntry (M : Matrix α α ℕ) (r c : α) (v : ℕ) :
    (setEntry M r c v).permanent = v * minorSum M r c + restSum M r c := by
  classical
  rw [Matrix.permanent, ← Finset.sum_filter_add_sum_filter_not univ
    (fun e : Equiv.Perm α => e c = r)]
  congr 1
  · rw [minorSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    simp only [Finset.mem_filter] at he
    rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ c), he.2]
    congr 1
    · simp [setEntry]
    · refine Finset.prod_congr rfl fun j hj => ?_
      exact setEntry_of_ne M r c v (by simp [Finset.ne_of_mem_erase hj])
  · rw [restSum]
    refine Finset.sum_congr rfl fun e he => ?_
    simp only [Finset.mem_filter] at he
    refine Finset.prod_congr rfl fun j _ => ?_
    refine setEntry_of_ne M r c v ?_
    rintro ⟨h1, rfl⟩
    exact he.2 h1

theorem permanent_eq_entry_mul (M : Matrix α α ℕ) (r c : α) :
    M.permanent = M r c * minorSum M r c + restSum M r c := by
  conv_lhs => rw [← setEntry_eq_self M r c]
  exact permanent_setEntry M r c (M r c)

/-- The gadget matrix: one unit of the weight at position `(r, c)` is moved onto an extra
row and column. -/
def border (A : Matrix α α ℕ) (r c : α) : Matrix (Option α) (Option α) ℕ :=
  fun i j =>
    match i, j with
    | some i', some j' => setEntry A r c (A r c - 1) i' j'
    | some i', none => if i' = r then 1 else 0
    | none, some j' => if j' = c then 1 else 0
    | none, none => 1

omit [Fintype α] in
@[simp] theorem border_some_some (A : Matrix α α ℕ) (r c i j : α) :
    border A r c (some i) (some j) = setEntry A r c (A r c - 1) i j := rfl

omit [Fintype α] in
@[simp] theorem border_some_none (A : Matrix α α ℕ) (r c i : α) :
    border A r c (some i) none = if i = r then 1 else 0 := rfl

omit [Fintype α] in
@[simp] theorem border_none_some (A : Matrix α α ℕ) (r c j : α) :
    border A r c none (some j) = if j = c then 1 else 0 := rfl

omit [Fintype α] in
@[simp] theorem border_none_none (A : Matrix α α ℕ) (r c : α) :
    border A r c none none = 1 := rfl

theorem prod_border_none (A : Matrix α α ℕ) (r c : α) (e : Equiv.Perm α) :
    (∏ i : Option α, border A r c ((Equiv.Perm.decomposeOption.symm (none, e)) i) i)
      = ∏ j : α, setEntry A r c (A r c - 1) (e j) j := by
  rw [Fintype.prod_option]
  simp

theorem prod_border_someR (A : Matrix α α ℕ) (r c : α) (e : Equiv.Perm α) :
    (∏ i : Option α, border A r c ((Equiv.Perm.decomposeOption.symm (some r, e)) i) i)
      = if e c = r then ∏ j ∈ univ.erase c, A (e j) j else 0 := by
  classical
  have hval : ∀ i : Option α,
      (Equiv.Perm.decomposeOption.symm (some r, e)) i = Equiv.swap none (some r) (i.map e) := by
    intro i
    simp [Equiv.Perm.decomposeOption]
  rw [Fintype.prod_option]
  have h0 : border A r c ((Equiv.Perm.decomposeOption.symm (some r, e)) none) none = 1 := by
    rw [hval]; simp
  rw [h0, one_mul]
  by_cases hec : e c = r
  · rw [if_pos hec, ← Finset.mul_prod_erase univ _ (Finset.mem_univ c)]
    have hc : border A r c ((Equiv.Perm.decomposeOption.symm (some r, e)) (some c)) (some c) = 1 := by
      rw [hval]
      simp [hec]
    rw [hc, one_mul]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjc : j ≠ c := Finset.ne_of_mem_erase hj
    have hej : e j ≠ r := by
      intro h
      exact hjc (e.injective (by rw [h, hec]))
    rw [hval]
    simp only [Option.map_some]
    rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simp [hej])]
    rw [border_some_some, setEntry_of_ne _ _ _ _ (by tauto)]
  · rw [if_neg hec]
    refine Finset.prod_eq_zero (Finset.mem_univ (e.symm r)) ?_
    rw [hval]
    have h1 : e (e.symm r) = r := by simp
    simp only [Option.map_some, h1]
    rw [Equiv.swap_apply_right]
    rw [border_none_some, if_neg]
    intro hcon
    exact hec (by rw [← hcon]; simp)

theorem prod_border_someOther (A : Matrix α α ℕ) (r c : α) (i₀ : α) (hi₀ : i₀ ≠ r)
    (e : Equiv.Perm α) :
    (∏ i : Option α, border A r c ((Equiv.Perm.decomposeOption.symm (some i₀, e)) i) i) = 0 := by
  classical
  have hval : (Equiv.Perm.decomposeOption.symm (some i₀, e)) none = some i₀ := by
    simp [Equiv.Perm.decomposeOption]
  rw [Fintype.prod_option, hval, border_some_none, if_neg hi₀, zero_mul]

/-- Key gadget identity: the bordered matrix has the same permanent as the original one. -/
theorem permanent_border (A : Matrix α α ℕ) (r c : α) (h : 1 ≤ A r c) :
    (border A r c).permanent = A.permanent := by
  classical
  have expand : (border A r c).permanent
      = ∑ p : Option α × Equiv.Perm α,
          ∏ i : Option α, border A r c ((Equiv.Perm.decomposeOption.symm p) i) i := by
    rw [Matrix.permanent]
    exact (Equiv.sum_comp (Equiv.Perm.decomposeOption.symm)
      (fun σ => ∏ i, border A r c (σ i) i)).symm
  rw [expand, Fintype.sum_prod_type, Fintype.sum_option]
  have hfirst : (∑ e : Equiv.Perm α,
      ∏ i : Option α, border A r c ((Equiv.Perm.decomposeOption.symm (none, e)) i) i)
      = (setEntry A r c (A r c - 1)).permanent := by
    rw [Matrix.permanent]
    exact Finset.sum_congr rfl fun e _ => prod_border_none A r c e
  have hsecond : (∑ i₀ : α, ∑ e : Equiv.Perm α,
      ∏ i : Option α, border A r c ((Equiv.Perm.decomposeOption.symm (some i₀, e)) i) i)
      = minorSum A r c := by
    rw [Finset.sum_eq_single r]
    · rw [minorSum, Finset.sum_filter]
      exact Finset.sum_congr rfl fun e _ => prod_border_someR A r c e
    · intro i₀ _ hi₀
      refine Finset.sum_eq_zero fun e _ => prod_border_someOther A r c i₀ hi₀ e
    · intro hcon
      exact absurd (Finset.mem_univ r) hcon
  rw [hfirst, hsecond, permanent_setEntry, permanent_eq_entry_mul A r c]
  have : A r c - 1 + 1 = A r c := by omega
  nlinarith [this]

/-! ## Eliminating all weights -/

/-- How far the entries of `A` are from being `0/1`. -/
def excess (A : Matrix α α ℕ) : ℕ := ∑ p : α × α, (A p.1 p.2 - 1)

omit [DecidableEq α] in
theorem entries_le_one_of_excess_zero {A : Matrix α α ℕ} (h : excess A = 0) (i j : α) :
    A i j ≤ 1 := by
  rw [excess] at h
  have h2 : A i j - 1 = 0 := Finset.sum_eq_zero_iff.1 h (i, j) (Finset.mem_univ _)
  omega

theorem excess_eq_sum_sum {γ : Type} [Fintype γ] (M : Matrix γ γ ℕ) :
    excess M = ∑ i : γ, ∑ j : γ, (M i j - 1) := by
  rw [excess, Fintype.sum_prod_type]

theorem excess_border (A : Matrix α α ℕ) (r c : α) :
    excess (border A r c) = excess (setEntry A r c (A r c - 1)) := by
  classical
  rw [excess_eq_sum_sum, excess_eq_sum_sum, Fintype.sum_option]
  have h1 : (∑ j : Option α, (border A r c none j - 1)) = 0 := by
    rw [Fintype.sum_option]
    simp only [border_none_none, border_none_some]
    refine by simp [Finset.sum_eq_zero, apply_ite (fun x : ℕ => x - 1)]
  rw [h1, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_option]
  simp only [border_some_none, border_some_some, apply_ite (fun x : ℕ => x - 1)]
  simp

theorem excess_setEntry_pred {A : Matrix α α ℕ} {r c : α} (h : 2 ≤ A r c) :
    excess (setEntry A r c (A r c - 1)) + 1 = excess A := by
  classical
  rw [excess, excess, ← Finset.sum_erase_add _ _ (Finset.mem_univ (r, c)),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (r, c))]
  have hbody : ∀ p ∈ (univ : Finset (α × α)).erase (r, c),
      (setEntry A r c (A r c - 1) p.1 p.2 - 1) = (A p.1 p.2 - 1) := by
    intro p hp
    have : ¬(p.1 = r ∧ p.2 = c) := by
      intro hcon
      exact (Finset.ne_of_mem_erase hp) (Prod.ext hcon.1 hcon.2)
    rw [setEntry_of_ne _ _ _ _ this]
  rw [Finset.sum_congr rfl hbody]
  simp only [setEntry_self]
  omega

theorem excess_border_lt {A : Matrix α α ℕ} {r c : α} (h : 2 ≤ A r c) :
    excess (border A r c) < excess A := by
  rw [excess_border]
  have := excess_setEntry_pred h
  omega

/-- Auxiliary induction: a matrix of `excess` at most `k` has the same permanent as a `0/1`
matrix of size at most `card γ + k`. -/
theorem exists_01_matrix_aux (k : ℕ) :
    ∀ (γ : Type) [Fintype γ] [DecidableEq γ] (A : Matrix γ γ ℕ), excess A ≤ k →
      ∃ (N : ℕ) (B : Matrix (Fin N) (Fin N) ℕ),
        N ≤ Fintype.card γ + k ∧ (∀ i j, B i j ≤ 1) ∧ B.permanent = A.permanent := by
  induction k with
  | zero =>
      intro γ _ _ A hA
      have h0 : excess A = 0 := Nat.le_zero.1 hA
      exact ⟨Fintype.card γ,
        A.submatrix (Fintype.equivFin γ).symm (Fintype.equivFin γ).symm, by omega,
        fun i j => entries_le_one_of_excess_zero h0 _ _, permanent_submatrix_equiv _ _⟩
  | succ k ih =>
      intro γ _ _ A hA
      by_cases h : ∀ i j, A i j ≤ 1
      · exact ⟨Fintype.card γ,
          A.submatrix (Fintype.equivFin γ).symm (Fintype.equivFin γ).symm, by omega,
          fun i j => h _ _, permanent_submatrix_equiv _ _⟩
      · push_neg at h
        obtain ⟨r, c, hrc⟩ := h
        have h2 : 2 ≤ A r c := hrc
        have hlt := excess_border_lt (A := A) h2
        obtain ⟨N, B, hN, h01, hper⟩ := ih (Option γ) (border A r c) (by omega)
        refine ⟨N, B, ?_, h01, ?_⟩
        · rw [Fintype.card_option] at hN
          omega
        · rw [hper, permanent_border A r c (by omega)]

/-- **Weight elimination.** The permanent of an arbitrary matrix of natural numbers equals the
permanent of a `0/1` matrix whose size is bounded by the size of the original matrix plus the
total excess of its entries.  Hence the `0/1` permanent is at least as hard to compute as the
permanent of nonnegative integer matrices (given in unary). -/
theorem exists_01_permanent (A : Matrix α α ℕ) :
    ∃ (N : ℕ) (B : Matrix (Fin N) (Fin N) ℕ),
      N ≤ Fintype.card α + excess A ∧ (∀ i j, B i j ≤ 1) ∧ B.permanent = A.permanent :=
  exists_01_matrix_aux (excess A) α A le_rfl

end CS

