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

theorem ustcon_in_logspace (h : HasPolyUES) :
    ∃ c : ℕ, ∀ (n d : ℕ) [NeZero d], ∃ M : Machine n d,
      M.numConfigs ≤ (n * d + 2) ^ c ∧
      M.space ≤ c * (Nat.log 2 (n * d + 2) + 1) ∧
      ∀ (G : RotGraph n d) (s t : Fin n), M.Accepts G s t ↔ G.Reachable s t := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c + 5, ?_⟩
  intro n d _
  obtain ⟨T, seq, hT, hues⟩ := hc n d
  refine ⟨Machine.connMachine n d T seq, ?_, ?_, ?_⟩
  · rw [Machine.connMachine_numConfigs]
    exact numConfigs_bound (Nat.pos_of_ne_zero (NeZero.ne d)) hT
  · refine log_le_of_le_pow ?_
    rw [Machine.connMachine_numConfigs]
    exact numConfigs_bound (Nat.pos_of_ne_zero (NeZero.ne d)) hT
  · intro G s t
    exact Machine.connMachine_correct hues G s t

/-! ## Symmetric nondeterministic machines: `SL ⊆ L` -/

/-- A symmetric nondeterministic space-bounded machine: its configuration graph is an
undirected `d`-regular multigraph on the (finite) configuration type, presented by a rotation
map, with a distinguished initial configuration and a distinguished accepting configuration
(the standard normalisation of a symmetric machine). -/
structure SymMachine (d : ℕ) where
  /-- The configuration type. -/
  C : Type
  /-- The configuration type is finite. -/
  fintypeC : Fintype C
  /-- The rotation map of the configuration graph. -/
  rot : C × Fin d → C × Fin d
  /-- Symmetry of the configuration graph. -/
  rot_involutive : Function.Involutive rot
  /-- The initial configuration. -/
  start : C
  /-- The unique accepting configuration. -/
  acc : C

namespace SymMachine

variable {d : ℕ}

/-- The number of configurations. -/
