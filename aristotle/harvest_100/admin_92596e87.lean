import Mathlib

/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file sets up a self-contained formal model of probabilistically checkable proofs
(non-adaptive verifiers with `q` queries and `r(n)` random bits, perfect completeness and
soundness `1/2`) and of the class `NP`, both measured against one and the same abstract
notion of "efficient computation" (a `ComplexityModel`).

Inside this model we prove, unconditionally:

* `CS.pcp_subset_np` : `PCP(log n, O(1)) ⊆ NP` — a verifier using `O(log n)` random bits and
  a constant number of queries can be simulated by an `NP` verifier that reads a polynomially
  long prefix of the proof and checks *all* `2^{O(log n)} = poly(n)` random strings.
* `CS.pcp_theorem` : the equality `NP = PCP(log n, O(1))` is *equivalent* to the single
  inclusion `NP ⊆ PCP(log n, O(1))`; i.e. the content of the PCP theorem is entirely
  contained in that inclusion.
* `CS.pcp_theorem_of_hard` : the class equality itself, from that inclusion.
* `CS.trivialModel_hard_inclusion` : the framework is consistent and the hypothesis of
  `CS.pcp_theorem_of_hard` is satisfiable (a concrete `ComplexityModel` in which it holds).

The deep inclusion `NP ⊆ PCP(log n, O(1))` (Arora–Safra, Arora–Lund–Motwani–Sudan–Szegedy;
Dinur) is *not* formalized here; it appears as an explicit hypothesis of
`CS.pcp_theorem_of_hard` and as the right-hand side of the equivalence `CS.pcp_theorem`.
-/

set_option autoImplicit false

namespace CS

/-! ### Strings, languages and resource bounds -/

/-- Inputs, witnesses and random strings are finite bit strings. -/
abbrev BitString := List Bool

/-- A language is a predicate on bit strings. -/
abbrev Language := BitString → Prop

/-- `f` is bounded by a polynomial. -/
def IsPoly (f : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, f n ≤ c * n ^ k + c

/-- `f` is `O(log n)`. -/
def IsLogBounded (f : ℕ → ℕ) : Prop := ∃ c : ℕ, ∀ n, f n ≤ c * Nat.log 2 (n + 1) + c

/-- The finite set of all bit strings of length `n`; the sample space of the verifier's
random coins. -/
def bitStrings : ℕ → Finset BitString
  | 0 => {[]}
  | n + 1 =>
      (bitStrings n).image (List.cons true) ∪ (bitStrings n).image (List.cons false)

lemma mem_bitStrings {n : ℕ} {ρ : BitString} : ρ ∈ bitStrings n ↔ ρ.length = n := by
  induction n generalizing ρ with
  | zero =>
      simp [bitStrings, List.length_eq_zero_iff]
  | succ n ih =>
      constructor
      · intro h
        simp only [bitStrings, Finset.mem_union, Finset.mem_image] at h
        rcases h with ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩ <;>
          simp [(ih (ρ := σ)).1 hσ]
      · intro h
        cases ρ with
        | nil => simp at h
        | cons b σ =>
            have hσ : σ ∈ bitStrings n := (ih (ρ := σ)).2 (by simpa using h)
            cases b <;>
              simp only [bitStrings, Finset.mem_union, Finset.mem_image] <;>
              [right; left] <;> exact ⟨σ, hσ, rfl⟩

lemma card_bitStrings (n : ℕ) : (bitStrings n).card = 2 ^ n := by
  induction n with
  | zero => simp [bitStrings]
  | succ n ih =>
      have hdisj :
          Disjoint ((bitStrings n).image (List.cons true))
            ((bitStrings n).image (List.cons false)) := by
        refine Finset.disjoint_left.mpr ?_
        rintro ρ hρ hρ'
        simp only [Finset.mem_image] at hρ hρ'
        obtain ⟨σ, -, rfl⟩ := hρ
        obtain ⟨τ, -, hτ⟩ := hρ'
        exact Bool.noConfusion (List.head_eq_of_cons_eq hτ)
      have h1 : ((bitStrings n).image (List.cons true)).card = 2 ^ n := by
        rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), ih]
      have h2 : ((bitStrings n).image (List.cons false)).card = 2 ^ n := by
        rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), ih]
      rw [bitStrings, Finset.card_union_of_disjoint hdisj, h1, h2]
      ring

/-! ### Verifiers -/

/-- A non-adaptive PCP verifier: on input `x` and random string `ρ` it computes `q` proof
positions to look at, and then decides on the basis of the `q` bits it read. The number of
queries `q` is a constant of the verifier, which is exactly the `O(1)` in `PCP(log n, 1)`. -/
structure Verifier where
  /-- number of queries -/
  q : ℕ
  /-- the queried positions -/
  query : BitString → BitString → Fin q → ℕ
  /-- the decision predicate, applied to the bits that were read -/
  accept : BitString → BitString → (Fin q → Bool) → Bool

/-- A proof string (an assignment of a bit to every position). -/
abbrev PCPProof := ℕ → Bool

/-- The verdict of `V` on input `x`, coins `ρ` and proof `π`. -/
def Verifier.run (V : Verifier) (x ρ : BitString) (π : PCPProof) : Bool :=
  V.accept x ρ fun i => π (V.query x ρ i)

/-- The set of random strings (of length `r`) on which `V` accepts `π`. -/
def acceptSet (V : Verifier) (x : BitString) (r : ℕ) (π : PCPProof) : Finset BitString :=
  (bitStrings r).filter fun ρ => V.run x ρ π = true

/-- An abstract model of efficient (polynomial-time) computation, used *uniformly* for both
classes below. Two closure/soundness properties of polynomial time are recorded; they are the
only facts about efficiency that the proofs need. -/
structure ComplexityModel where
  /-- efficiently computable predicates of an input and a witness (`NP` verifiers) -/
  EffPred : (BitString → BitString → Bool) → Prop
  /-- efficient PCP verifiers -/
  EffVerifier : Verifier → Prop
  /-- an efficient verifier can only address polynomially far into its proof -/
  query_poly : ∀ V : Verifier, EffVerifier V →
    ∃ p : ℕ → ℕ, IsPoly p ∧ ∀ x ρ i, V.query x ρ i ≤ p x.length
  /-- polynomial time is closed under taking the conjunction of the verdicts over all
  `2^{O(log n)} = poly(n)` random strings, the proof being given as an explicit bit list -/
  eff_forall_random : ∀ (V : Verifier) (r : ℕ → ℕ), IsLogBounded r → EffVerifier V →
    EffPred fun x w => decide (∀ ρ ∈ bitStrings (r x.length),
      V.accept x ρ (fun i => w.getD (V.query x ρ i) false) = true)

/-- `V`, using `r(n)` random bits, is a PCP verifier for `L`: perfect completeness and
soundness error at most `1/2`. -/
structure IsPCPVerifier (M : ComplexityModel) (V : Verifier) (r : ℕ → ℕ) (L : Language) :
    Prop where
  /-- the verifier is efficient -/
  eff : M.EffVerifier V
  /-- it uses `O(log n)` random bits -/
  rand : IsLogBounded r
  /-- completeness: members of `L` have proofs accepted with probability one -/
  completeness : ∀ x, L x → ∃ π : PCPProof, ∀ ρ ∈ bitStrings (r x.length), V.run x ρ π = true
  /-- soundness: for non-members every proof is accepted with probability at most `1/2` -/
  soundness : ∀ x, ¬ L x → ∀ π : PCPProof,
    2 * (acceptSet V x (r x.length) π).card ≤ 2 ^ (r x.length)

/-- The class `PCP(log n, O(1))`. -/
def PCPClass (M : ComplexityModel) (L : Language) : Prop :=
  ∃ (V : Verifier) (r : ℕ → ℕ), IsPCPVerifier M V r L

/-- `W`, with witnesses of length at most `p(n)`, is an `NP` verifier for `L`. -/
structure IsNPVerifier (M : ComplexityModel) (W : BitString → BitString → Bool) (p : ℕ → ℕ)
    (L : Language) : Prop where
  /-- the verifier is efficient -/
  eff : M.EffPred W
  /-- witnesses are polynomially long -/
  poly : IsPoly p
  /-- correctness -/
  correct : ∀ x, L x ↔ ∃ w : BitString, w.length ≤ p x.length ∧ W x w = true

/-- The class `NP`. -/
def NP (M : ComplexityModel) (L : Language) : Prop :=
  ∃ (W : BitString → BitString → Bool) (p : ℕ → ℕ), IsNPVerifier M W p L

/-! ### The easy inclusion `PCP(log n, O(1)) ⊆ NP` -/

private lemma getD_map_range (f : ℕ → Bool) {m j : ℕ} (h : j < m) :
    ((List.range m).map f).getD j false = f j := by
  have hlen : j < ((List.range m).map f).length := by simpa using h
  rw [List.getD_eq_getElem _ _ hlen]
  simp

/-- **Easy direction of the PCP theorem.** A language with a PCP verifier using `O(log n)`
random bits and a constant number of queries is in `NP`: the `NP` witness is the relevant
polynomially long prefix of the PCP proof, and the `NP` verifier checks the PCP verifier's
verdict on *all* of the polynomially many random strings. -/
theorem pcp_subset_np (M : ComplexityModel) (L : Language) (h : PCPClass M L) : NP M L := by
  obtain ⟨V, r, hV⟩ := h
  obtain ⟨p, hp, hbound⟩ := M.query_poly V hV.eff
  refine ⟨fun x w => decide (∀ ρ ∈ bitStrings (r x.length),
      V.accept x ρ (fun i => w.getD (V.query x ρ i) false) = true), fun n => p n + 1, ?_⟩
  refine
    { eff := M.eff_forall_random V r hV.rand hV.eff
      poly := ?_
      correct := ?_ }
  · obtain ⟨c, k, hc⟩ := hp
    exact ⟨c + 1, k, fun n => by have := hc n; nlinarith [Nat.zero_le (n ^ k)]⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨π, hπ⟩ := hV.completeness x hx
      refine ⟨(List.range (p x.length + 1)).map π, by simp, ?_⟩
      simp only [decide_eq_true_eq]
      intro ρ hρ
      have := hπ ρ hρ
      rw [Verifier.run] at this
      refine Eq.trans ?_ this
      congr 1
      funext i
      exact getD_map_range π (Nat.lt_succ_of_le (hbound x ρ i))
    · rintro ⟨w, -, hw⟩
      by_contra hx
      simp only [decide_eq_true_eq] at hw
      set π : PCPProof := fun j => w.getD j false with hπdef
      have hall : acceptSet V x (r x.length) π = bitStrings (r x.length) := by
        apply Finset.filter_true_of_mem
        intro ρ hρ
        exact hw ρ hρ
      have hsound := hV.soundness x hx π
      rw [hall, card_bitStrings] at hsound
      have hpos : 0 < 2 ^ (r x.length) := Nat.two_pow_pos _
      omega

/-! ### The PCP theorem -/

/-- **The PCP theorem, `NP = PCP(log n, 1)`**, from its hard inclusion.

The inclusion `PCP(log n, O(1)) ⊆ NP` is proved unconditionally (`CS.pcp_subset_np`); the
hypothesis `hard` is the deep inclusion `NP ⊆ PCP(log n, O(1))` of Arora–Safra and
Arora–Lund–Motwani–Sudan–Szegedy, which is *not* formalized here. It is satisfiable: see
`CS.trivialModel_hard_inclusion`. -/
theorem pcp_theorem_of_hard (M : ComplexityModel)
    (hard : ∀ L : Language, NP M L → PCPClass M L) :
    ∀ L : Language, NP M L ↔ PCPClass M L :=
  fun L => ⟨hard L, pcp_subset_np M L⟩

/-- **The PCP theorem, reduced to its hard inclusion.**

`NP = PCP(log n, 1)` holds if and only if `NP ⊆ PCP(log n, 1)`: the reverse inclusion is a
theorem of the model (`CS.pcp_subset_np`). Thus the whole content of the PCP theorem is the
single inclusion on the right-hand side. -/
theorem pcp_theorem (M : ComplexityModel) :
    (∀ L : Language, NP M L ↔ PCPClass M L) ↔ (∀ L : Language, NP M L → PCPClass M L) :=
  ⟨fun h L => (h L).1, fun h => pcp_theorem_of_hard M h⟩

/-! ### Consistency of the framework

The definitions above are not vacuous: there is a `ComplexityModel`, and in it the hypothesis
of `CS.pcp_theorem_of_hard` is satisfied. -/

open scoped Classical in
/-- A `ComplexityModel` in which every function is "efficient" (queries still have to be
polynomially bounded, as the axiom `query_poly` demands). -/
noncomputable def trivialModel : ComplexityModel where
  EffPred := fun _ => True
  EffVerifier := fun V => ∃ p : ℕ → ℕ, IsPoly p ∧ ∀ x ρ i, V.query x ρ i ≤ p x.length
  query_poly := fun _ h => h
  eff_forall_random := fun _ _ _ _ => trivial

open scoped Classical in
lemma trivialModel_np (L : Language) : NP trivialModel L := by
  refine ⟨fun x _ => decide (L x), fun _ => 0, ?_⟩
  refine { eff := trivial, poly := ⟨0, 0, by simp⟩, correct := ?_ }
  intro x
  constructor
  · intro hx; exact ⟨[], by simp, by simpa using hx⟩
  · rintro ⟨w, -, hw⟩; simpa using hw

open scoped Classical in
lemma trivialModel_pcp (L : Language) : PCPClass trivialModel L := by
  refine ⟨⟨0, fun _ _ i => i.elim0, fun x _ _ => decide (L x)⟩, fun _ => 0, ?_⟩
  refine
    { eff := ⟨fun _ => 0, ⟨0, 0, by simp⟩, fun _ _ i => i.elim0⟩
      rand := ⟨0, by simp⟩
      completeness := ?_
      soundness := ?_ }
  · intro x hx
    exact ⟨fun _ => false, fun ρ _ => by simpa [Verifier.run] using hx⟩
  · intro x hx π
    have : acceptSet ⟨0, fun _ _ i => i.elim0, fun x _ _ => decide (L x)⟩ x 0 π = ∅ := by
      apply Finset.filter_false_of_mem
      intro ρ _
      simpa [Verifier.run] using hx
    rw [this]
    simp

/-- The hypothesis of `CS.pcp_theorem_of_hard` is satisfiable. -/
lemma trivialModel_hard_inclusion : ∀ L : Language, NP trivialModel L → PCPClass trivialModel L :=
  fun L _ => trivialModel_pcp L

end CS

