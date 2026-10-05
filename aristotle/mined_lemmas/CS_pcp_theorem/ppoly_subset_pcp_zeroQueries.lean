/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file formalises the statement `NP = PCP(log n, 1)` — the PCP theorem — in a
concrete non-uniform (Boolean circuit) model of computation.  The development is
self-contained and uses no imports.

* `CS.Circuit` : Boolean circuits over an arbitrary type of input variables.
* `CS.NPVerifier` / `CS.NPpoly` : the class of languages possessing a
  polynomial-size verifier reading a polynomially long witness (the non-uniform
  version of `NP`).
* `CS.PCPVerifier` / `CS.PCPlogConst` : probabilistically checkable proof systems
  with logarithmic randomness (equivalently, polynomially many random strings),
  polynomially long proofs, perfect completeness, soundness error `1/2`, and a
  prescribed bound on the number of proof bits inspected.  `PCPlogConst` is the
  class `PCP(log n, O(1))`, where the query bound is a constant independent of
  the input length.

Proved here:

* `CS.pcp_subset_np` : `PCP(log n, q) ⊆ NP` for every query bound (the "easy"
  inclusion; it is proved by taking the conjunction of the verifier's decision
  circuits over all of the polynomially many random strings).
* `CS.np_subset_pcp_polyQueries` : every `NP` language has a PCP system with
  logarithmic randomness and *polynomially many* queries (so the model is not
  degenerate, and the whole content of the PCP theorem is the reduction of the
  number of queries to a constant).
* `CS.ppoly_subset_pcplogconst` : every language decidable by polynomial-size
  circuits lies in `PCP(log n, O(1))` (with zero queries), so the latter class
  is non-empty.
* `CS.pcp_theorem` : the PCP theorem, `NP = PCP(log n, O(1))`.  The hard
  inclusion `NP ⊆ PCP(log n, O(1))` (Arora–Safra, Arora–Lund–Motwani–Sudan–Szegedy)
  is *not* proved here; it enters as an explicit hypothesis `hard` of the
  theorem, while the easy inclusion is supplied by `CS.pcp_subset_np`.
-/

namespace CS

/-! ## Polynomially bounded functions -/

/-- `PolyBdd f` : the function `f : ℕ → ℕ` is bounded by a polynomial. -/

theorem ppoly_subset_pcp_zeroQueries {L : Language} (h : Ppoly L) :
    Nonempty (PCPVerifier L (fun _ => 0)) := by
  have V := Classical.choice h
  refine ⟨?_⟩
  exact
  { plen := fun _ => 0
    hplen := PolyBdd.const 0
    rand := fun _ => 1
    hrand := PolyBdd.const 1
    hrandpos := fun _ => Nat.one_pos
    circ := fun n _ => (V.circ n).map Sum.inl
    szBound := V.szBound
    hszBound := V.hszBound
    hsize := by
      intro n _
      rw [Circuit.size_map]
      exact V.hsize n
    hquery := by
      intro n _ _
      exact ⟨[], Nat.le_refl 0, fun π π' _ => by
        simp only [Circuit.eval_map]
        rfl⟩
    completeness := by
      intro n x hx
      refine ⟨fun i => i.elim0, fun _ => ?_⟩
      rw [Circuit.eval_map]
      exact (V.correct n x).1 hx
    soundness := by
      intro n x hx π
      have hrej : ¬ (((V.circ n).map Sum.inl).eval (Sum.elim x π) = true) := by
        rw [Circuit.eval_map]
        intro hacc
        exact hx ((V.correct n x).2 hacc)
      have hzero : (List.finRange 1).countP
          (fun _ => ((V.circ n).map Sum.inl).eval (Sum.elim x π)) = 0 :=
        List.countP_eq_zero.2 (fun _ _ => hrej)
      simp only [hzero]
      omega }

/-- Languages decidable by polynomial-size circuits lie in `PCP(log n, O(1))`. -/
