/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Savitch.Model
import RequestProject.Savitch.Stack

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

`NSPACE f ⊆ DSPACE (f²)`.

Given a nondeterministic machine with at most `2 ^ (c * f n + c)` configurations we build a
deterministic machine which decides, by Savitch's midpoint recursion, whether an accepting
configuration is reachable in the configuration graph.  The deterministic machine stores an
explicit recursion stack of depth `c * f n + c + 2`, each frame holding a constant number of
configurations and indices, hence it has `2 ^ O(f n ^ 2)` configurations.

As a corollary, `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

section Construction

variable (M : NMachine)

/-- The vertices of the configuration graph: the configurations of `M`, together with an extra
sink `none` which is reachable exactly from the accepting configurations.  Thus `M` accepts iff
the sink is reachable from the initial configuration. -/
abbrev Vtx (M : NMachine) (n : ℕ) : Type := Option (M.Conf n)

instance vtxFinite (n : ℕ) : Finite (Vtx M n) := by
  haveI := M.finite n; infer_instance

noncomputable instance vtxFintype (n : ℕ) : Fintype (Vtx M n) := Fintype.ofFinite _

noncomputable instance vtxDecEq (n : ℕ) : DecidableEq (Vtx M n) := Classical.decEq _

/-- An enumeration of the vertices of the configuration graph. -/

theorem run_root (hl : ∀ x : X, x ∈ l) (K : ℕ) (u v : X) :
    (∃ t, saccept ((sstep badj l)^[t] ⟨[⟨K, u, v, 0, false⟩], none⟩) = true) ↔
      Reach (adjOf badj) K u v := by
  obtain ⟨t₀, b, ht₀, hb⟩ := run_frame hl K ⟨K, u, v, 0, false⟩ rfl []
  rw [fval_fresh hl] at hb
  constructor
  · rintro ⟨t, ht⟩
    have hstate : (sstep badj l)^[t] ⟨[⟨K, u, v, 0, false⟩], none⟩ = ⟨[], some true⟩ :=
      eq_of_saccept ht
    have h1 : (sstep badj l)^[max t t₀] (⟨[⟨K, u, v, 0, false⟩], none⟩ : SState X) =
        ⟨[], some true⟩ := by
      rw [show max t t₀ = (max t t₀ - t) + t by omega, Function.iterate_add_apply, hstate,
        sstep_iterate_nil]
    have h2 : (sstep badj l)^[max t t₀] (⟨[⟨K, u, v, 0, false⟩], none⟩ : SState X) =
        ⟨[], some b⟩ := by
      rw [show max t t₀ = (max t t₀ - t₀) + t₀ by omega, Function.iterate_add_apply, ht₀,
        sstep_iterate_nil]
    rw [h1] at h2
    have hbt : b = true := (Option.some.inj (congrArg SState.ret h2)).symm
    exact hb.1 hbt
  · intro h
    refine ⟨t₀, ?_⟩
    rw [ht₀]
    simp [saccept, hb.2 h]

/-! ### Bounding the number of configurations -/

/-- The levels of the frames on the stack increase by exactly one from the top to the bottom of
the stack, and the bottom frame has level at most `K`. -/
