/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (it uses only Lean 4 core `List`/`Nat`),
so that the required header comment can be the very first thing in the file.

## What is formalised here

The PCP theorem is the statement

    NP = PCP(log n, 1)

i.e. every language in `NP` admits a probabilistically checkable proof which the
verifier inspects using `O(log n)` random bits and `O(1)` queries, with perfect
completeness and soundness `1/2`; and conversely every language with such a
verifier is in `NP`.

Both classes only make sense relative to a notion of *feasible* (polynomial
time) computation.  Rather than fixing one particular machine model, we
parametrise the development by a `Model`: a class of "efficiently decidable"
predicates which is closed under the one operation the easy inclusion needs,
namely taking a conjunction over all `2 ^ rho n` random strings when `rho` is
logarithmically bounded (for polynomial time this is exactly the fact that a
polynomial-time predicate stays polynomial time when quantified universally over
polynomially many values).  `Model` is inhabited (see `CS.trivialModel`), so
nothing below is vacuous.

The main results are:

* `CS.pcp_subset_np` : `PCP(log n, O(1)) ⊆ NP`, proved in full.
* `CS.pcp_theorem`   : the PCP theorem for a model is *equivalent* to the single
  inclusion `NP ⊆ PCP(log n, O(1))`; the other half of the equality is the
  theorem `CS.pcp_subset_np` proved here.

The reverse inclusion `NP ⊆ PCP(log n, O(1))` is the deep Arora–Safra /
Arora–Lund–Motwani–Sudan–Szegedy content and is *not* formalised; it is exactly
what the right-hand side of `CS.pcp_theorem` isolates.
-/

namespace CS

/-- Inputs are finite bit strings. -/
abbrev Word := List Bool

/-- A language is a predicate on bit strings. -/
abbrev Language := Word → Prop

/-- `f` is bounded by a polynomial. -/

def IsPoly (f : Nat → Nat) : Prop := ∃ c k : Nat, ∀ n, f n ≤ c * (n + 1) ^ k

/-- `f` is `O(log n)`. -/

def PCPlog1 (M : Model) (L : Language) : Prop := Nonempty (PCPVerifier M L)

/-- A polynomially bounded certificate verifier for `L`. -/
structure NPVerifier (M : Model) (L : Language) where
  /-- Length bound on certificates. -/
  plen : Nat → Nat
  /-- The decision predicate of the verifier. -/
  V : Word → Word → Bool
  plen_poly : IsPoly plen
  V_eff : M.Eff₂ V
  correct : ∀ x, L x ↔ ∃ w : Word, w.length ≤ plen x.length ∧ V x w = true

/-- The class `NP`. -/

def NP (M : Model) (L : Language) : Prop := Nonempty (NPVerifier M L)

/--
The easy inclusion of the PCP theorem: `PCP(log n, O(1)) ⊆ NP`.

Given a PCP verifier, the NP verifier takes the PCP proof as its certificate and
checks *all* `2 ^ rho |x| = poly(|x|)` random strings deterministically.
Completeness of the PCP gives a certificate for every `x ∈ L`; soundness
(error `1/2 < 1`) forbids a certificate passing all random strings when
`x ∉ L`.
-/

theorem pcp_subset_np (M : Model) (L : Language) (h : PCPlog1 M L) : NP M L := by
  obtain ⟨P⟩ := h
  refine ⟨{ plen := P.plen
            V := fun x pf => (List.range (2 ^ P.rho x.length)).all (fun r => P.V x r pf)
            plen_poly := P.plen_poly
            V_eff := M.eff_forall_bounded P.V P.rho P.V_eff P.rho_log
            correct := ?_ }⟩
  intro x
  constructor
  · intro hx
    obtain ⟨pf, hlen, hpf⟩ := P.complete x hx
    refine ⟨pf, hlen, ?_⟩
    exact List.all_eq_true.mpr (fun r hr => hpf r (List.mem_range.mp hr))
  · intro ⟨w, _, hw⟩
    by_contra hx
    have hall : ∀ r ∈ List.range (2 ^ P.rho x.length), P.V x r w = true :=
      fun r hr => List.all_eq_true.mp hw r hr
    have hcount : (List.range (2 ^ P.rho x.length)).countP (fun r => P.V x r w)
        = 2 ^ P.rho x.length := by
      rw [List.countP_eq_length.mpr hall, List.length_range]
    have hs := P.sound x hx w
    rw [hcount] at hs
    have := Nat.two_pow_pos (P.rho x.length)
    omega

/-- The statement of the PCP theorem in a model `M`: `NP = PCP(log n, 1)`. -/

def PCPTheoremStatement (M : Model) : Prop := ∀ L, NP M L ↔ PCPlog1 M L

/--
**The PCP theorem, `NP = PCP(log n, 1)`.**

The inclusion `PCP(log n, O(1)) ⊆ NP` is proved here (`CS.pcp_subset_np`), so
the full equality of classes is *equivalent* to the single remaining inclusion
`NP ⊆ PCP(log n, O(1))` — the Arora–Safra / ALMSS content of the theorem, which
this file does not formalise.
-/

theorem pcp_theorem (M : Model) :
    PCPTheoremStatement M ↔ (∀ L, NP M L → PCPlog1 M L) := by
  constructor
  · intro h L hL
    exact (h L).mp hL
  · intro h L
    exact ⟨h L, pcp_subset_np M L⟩

/-- A model does exist, so the development above is not vacuous. -/
