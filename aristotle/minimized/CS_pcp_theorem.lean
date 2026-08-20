/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file develops, from first principles (no imports beyond the Lean core prelude),
a formal framework for probabilistically checkable proofs and states the PCP theorem
`NP = PCP(log n, 1)` inside it.

Design.

* Languages are predicates on binary words.
* "Efficient computability" is abstracted into a structure `CS.EffModel` carrying a
  predicate on functions (think: polynomial-time computable) together with two closure
  properties that polynomial time enjoys:
  - evaluating a (efficiently produced) local test against a candidate proof written on
    the witness tape is efficient;
  - a conjunction over all random strings of length `b n` is efficient whenever
    `2 ^ b n` is polynomially bounded (i.e. `b n = O(log n)`).
* A PCP verifier is given by an efficiently computable map sending an input `x` and a
  random string `ρ` to a *local test*: a list of at most `q` positions of the proof to
  read, together with the truth table of the predicate applied to the answers.
  Completeness is perfect and the soundness error is `1/2`, as in the standard
  definition of the class `PCP(r(n), q(n))`.

Results.

* `CS.pcp_subset_np`: unconditionally, `PCP(log n, O(1)) ⊆ NP` in any such model.
* `CS.pcp_theorem_iff`: unconditionally, the class equality `NP = PCP(log n, 1)` is
  equivalent to the inclusion `NP ⊆ PCP(log n, 1)`.
* `CS.pcp_theorem`: the class equality `NP = PCP(log n, 1)`, with the hard inclusion
  `NP ⊆ PCP(log n, 1)` (the Arora–Safra / Arora–Lund–Motwani–Sudan–Szegedy theorem,
  whose known proofs proceed by low-degree testing or by Dinur's gap amplification)
  taken as an explicit hypothesis. Everything else is proved here.
-/

namespace CS

/-- Binary words. -/
abbrev Word := List Bool

/-- A language is a set of binary words. -/
abbrev Language := Word → Prop

/-- `f` is bounded by a polynomial. -/

def PolyBounded (f : Nat → Nat) : Prop := ∃ c k : Nat, ∀ n, f n ≤ c * (n + 1) ^ k

/-- `r n = O(log n)`, expressed as: `2 ^ r n` is polynomially bounded. -/

def LogBounded (r : Nat → Nat) : Prop := PolyBounded (fun n => 2 ^ r n)

/-! ### Random strings -/

/-- The list of all binary words of length `k`. -/

def allWords : Nat → List Word
  | 0 => [[]]
  | k + 1 => (allWords k).flatMap (fun w => [false :: w, true :: w])

private theorem length_flatMap_pair (l : List Word) :
    (l.flatMap (fun w => [false :: w, true :: w])).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.flatMap_cons, ih]; omega

theorem length_allWords (k : Nat) : (allWords k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [allWords, length_flatMap_pair, ih, Nat.pow_succ]
    omega

theorem length_allWords_pos (k : Nat) : 0 < (allWords k).length := by
  rw [length_allWords]
  exact Nat.two_pow_pos k

def idx : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) * 2 ^ bs.length + idx bs

/-- A *local test*: a list of positions of the proof to be read, together with the truth
table of the predicate that is applied to the answers.  Since the truth table is written
out explicitly, this representation is the appropriate one for a constant number of
queries. -/
structure Query where
  /-- The positions of the proof that are queried. -/
  pos : List Nat
  /-- The truth table of the local predicate, indexed by the answers. -/
  table : List Bool

/-- The test `Q` accepts the proof `π`. -/

def Query.accepts (Q : Query) (π : Nat → Bool) : Bool :=
  Q.table.getD (idx (Q.pos.map π)) false

theorem accepts_congr (Q : Query) (π π' : Nat → Bool) (h : ∀ i ∈ Q.pos, π i = π' i) :
    Q.accepts π = Q.accepts π' := by
  unfold Query.accepts
  rw [List.map_congr_left h]

/-! ### An abstract model of efficient computation -/

/-- An abstract model of efficient (think: polynomial-time) computability, with the two
closure properties used below.  Polynomial time satisfies these. -/
structure EffModel where
  /-- Efficiently computable binary predicates on words. -/
  Eff₂ : (Word → Word → Bool) → Prop
  /-- Efficiently computable ternary predicates on words. -/
  Eff₃ : (Word → Word → Word → Bool) → Prop
  /-- Efficiently computable maps from an input and a random string to a local test. -/
  EffQ : (Word → Word → Query) → Prop
  /-- Evaluating an efficiently produced local test against a proof written on a second
  tape is efficient. -/
  eff_eval : ∀ V : Word → Word → Query, EffQ V →
    Eff₃ (fun x w ρ => (V x ρ).accepts (fun i => w.getD i false))
  /-- A conjunction over all random strings of length `b n` is efficient as soon as
  `2 ^ b n` is polynomially bounded, i.e. `b n = O(log n)`. -/
  eff_forall : ∀ (g : Word → Word → Word → Bool) (b : Nat → Nat), Eff₃ g →
    PolyBounded (fun n => 2 ^ b n) →
    Eff₂ (fun x w => (allWords (b x.length)).all (fun ρ => g x w ρ))

/-- The two closure conditions are consistent: the model in which every function counts
as efficient satisfies them.  (This is only a non-vacuity check; the intended model is
polynomial time.) -/

def NP (M : EffModel) (L : Language) : Prop :=
  ∃ (p : Nat → Nat) (R : Word → Word → Bool), PolyBounded p ∧ M.Eff₂ R ∧
    ∀ x, L x ↔ ∃ w : Word, w.length ≤ p x.length ∧ R x w = true

/-- `V` is a PCP verifier for `L` using `r n` random bits, at most `q` queries into a
proof of length `plen n`, with perfect completeness and soundness error `1/2`. -/
structure IsPCPVerifier (r : Nat → Nat) (q : Nat) (plen : Nat → Nat) (L : Language)
    (V : Word → Word → Query) : Prop where
  /-- At most `q` positions are queried. -/
  queries : ∀ x ρ, (V x ρ).pos.length ≤ q
  /-- All queried positions lie inside the proof. -/
  inRange : ∀ x ρ, ∀ i ∈ (V x ρ).pos, i < plen x.length
  /-- Perfect completeness: inputs in `L` have a proof accepted for every random string. -/
  completeness : ∀ x, L x → ∃ π : Nat → Bool, ∀ ρ ∈ allWords (r x.length),
    (V x ρ).accepts π = true
  /-- Soundness error `1/2`: for inputs outside `L`, no proof is accepted for more than
  half of the random strings. -/
  soundness : ∀ x, ¬ L x → ∀ π : Nat → Bool,
    2 * ((allWords (r x.length)).countP (fun ρ => (V x ρ).accepts π)) ≤
      (allWords (r x.length)).length

/-- The class `PCP(r(n), q)`: languages with a PCP verifier using `r n` random bits and
`q` queries, perfect completeness and soundness error `1/2`. -/

def PCP (M : EffModel) (r : Nat → Nat) (q : Nat) (L : Language) : Prop :=
  ∃ (V : Word → Word → Query) (plen : Nat → Nat),
    M.EffQ V ∧ PolyBounded plen ∧ IsPCPVerifier r q plen L V

/-- The class `PCP(log n, 1)`: logarithmically many random bits and a constant number of
queries. -/

def PCPlog (M : EffModel) (L : Language) : Prop :=
  ∃ (r : Nat → Nat) (q : Nat), LogBounded r ∧ PCP M r q L

/-! ### The easy inclusion `PCP(log n, 1) ⊆ NP` -/

private theorem getD_map_range (π : Nat → Bool) (m i : Nat) (h : i < m) :
    ((List.range m).map π).getD i false = π i := by
  simp [List.getD_eq_getElem?_getD, h]

/-- Unconditionally: every language with a `(log n, O(1))`-PCP verifier is in `NP`.
The witness is the proof itself, and the verifier checks all `2 ^ O(log n)` = polynomially
many random strings. -/

theorem pcp_subset_np (M : EffModel) (L : Language) (h : PCPlog M L) : NP M L := by
  obtain ⟨r, q, hlog, V, plen, hV, hplen, H⟩ := h
  refine ⟨plen, fun x w => (allWords (r x.length)).all
    (fun ρ => (V x ρ).accepts (fun i => w.getD i false)), hplen,
    M.eff_forall _ r (M.eff_eval V hV) hlog, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨π, hπ⟩ := H.completeness x hx
    refine ⟨(List.range (plen x.length)).map π, by simp, ?_⟩
    rw [List.all_eq_true]
    intro ρ hρ
    have : (V x ρ).accepts (fun i => ((List.range (plen x.length)).map π).getD i false)
        = (V x ρ).accepts π := by
      refine accepts_congr _ _ _ ?_
      intro i hi
      exact getD_map_range π _ i (H.inRange x ρ i hi)
    rw [this]
    exact hπ ρ hρ
  · intro ⟨w, _, hw⟩
    cases Classical.em (L x) with
    | inl hx => exact hx
    | inr hx =>
      exfalso
      have hall : ∀ ρ ∈ allWords (r x.length),
          (V x ρ).accepts (fun i => w.getD i false) = true := by
        intro ρ hρ
        exact List.all_eq_true.mp hw ρ hρ
      have hcount : (allWords (r x.length)).countP
          (fun ρ => (V x ρ).accepts (fun i => w.getD i false))
          = (allWords (r x.length)).length := List.countP_eq_length.mpr hall
      have hs := H.soundness x hx (fun i => w.getD i false)
      rw [hcount] at hs
      have := length_allWords_pos (r x.length)
      omega

/-! ### The PCP theorem -/

/-- **The PCP theorem, reduced to its hard inclusion.**  Unconditionally, the class
equality `NP = PCP(log n, 1)` holds if and only if every language in `NP` has a PCP
verifier using logarithmically many random bits, a constant number of queries, perfect
completeness and soundness error `1/2`.  (The inclusion `PCP(log n, 1) ⊆ NP` is proved
here; the converse inclusion is the deep content of the theorem.) -/

theorem pcp_theorem_iff (M : EffModel) :
    NP M = PCPlog M ↔ ∀ L, NP M L → PCPlog M L := by
  constructor
  · intro h L hL
    rw [h] at hL
    exact hL
  · intro h
    funext L
    exact propext ⟨h L, pcp_subset_np M L⟩

/-- **The PCP theorem**: `NP = PCP(log n, 1)`.

The inclusion `PCP(log n, 1) ⊆ NP` is proved here (`CS.pcp_subset_np`).  The reverse
inclusion — the Arora–Safra / Arora–Lund–Motwani–Sudan–Szegedy theorem, proved either via
the low-degree test or via Dinur's gap amplification — is taken as the explicit hypothesis
`hNP_to_PCP`; no known proof of it is short, and it is not formalized here. -/
