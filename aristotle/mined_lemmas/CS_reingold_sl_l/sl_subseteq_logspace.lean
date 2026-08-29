import Mathlib
import RequestProject.ReingoldSlL

/-!
## Existence of universal exploration sequences

The hypothesis `CS.HasPolyUES` used in `RequestProject/ReingoldSlL.lean` asks for universal
exploration sequences of *polynomial* length; producing such short sequences is the deep part
of Reingold's theorem and is not formalised.  Here we prove, unconditionally, that universal
exploration sequences of *some* finite length always exist (`CS.exists_ues`).  This shows that
the notion is satisfiable — the only missing ingredient in `CS.HasPolyUES` is the polynomial
length bound.
-/

set_option autoImplicit false

namespace CS

namespace RotGraph

variable {n d : ℕ}

/-- The walk of length `k` only depends on the first `k` offsets. -/

theorem sl_subseteq_logspace (h : HasPolyUES) :
    ∃ c : ℕ, ∀ (d : ℕ) [NeZero d] (S : SymMachine d), ∃ M : DetMachine,
      M.numConfigs ≤ (S.numConfigs * d + 2) ^ c ∧
      M.space ≤ c * (Nat.log 2 (S.numConfigs * d + 2) + 1) ∧
      (M.Accepts ↔ S.Accepts) := by
  obtain ⟨c, hc⟩ := ustcon_in_logspace h
  refine ⟨c, ?_⟩
  intro d _ S
  letI := S.fintypeC
  obtain ⟨M, hcard, hspace, hcorrect⟩ := hc (Fintype.card S.C) d
  set e : S.C ≃ Fin (Fintype.card S.C) := Fintype.equivFin S.C with he
  refine ⟨M.toDet S.toRotGraph (e S.start) (e S.acc), ?_, ?_, ?_⟩
  · rw [Machine.toDet_numConfigs]
    exact hcard
  · rw [DetMachine.space, Machine.toDet_numConfigs]
    exact hspace
  · rw [Machine.toDet_accepts_iff, hcorrect]
    exact S.reachable_iff S.start S.acc

/-- **Reingold's theorem** (conditional on the universal exploration sequences produced by the
zig-zag construction, `HasPolyUES`): undirected `s`-`t` connectivity is decidable in
logarithmic space, and consequently every symmetric nondeterministic space-bounded machine can
be simulated deterministically with only a constant-factor increase of the space, i.e.
`SL ⊆ L`. -/
