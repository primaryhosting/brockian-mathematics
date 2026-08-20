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
import RequestProject.Savitch.Enc

/-!
# The Savitch simulator and its correctness

We build, from a nondeterministic machine `M` and a recursion depth `K`, a
deterministic machine `savitchDM M K` which decides, by Savitch's recursive midpoint
search, whether the sink vertex `none` of the configuration graph of `M` is reachable
from the start vertex within `2 ^ K` steps.  If `cV M ≤ 2 ^ K` this is exactly
acceptance by `M`.
-/

namespace CS
namespace Savitch

variable {Sigma : Type}


theorem wf_rawStep {M : NMachine Sigma} {K : ℕ} (o : Option Sigma) {s : Raw M}
    (h : WFraw M K s) : WFraw M K (rawStep M o s) := by
  obtain ⟨m, st⟩ := s
  match m, st with
  | Mode.call u v 0, st => exact h.2
  | Mode.call u v (i + 1), st =>
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ?_, cV_pos M, h2⟩
      · show i + (st.length + 1) ≤ K
        omega
      · show i + st.length + 1 ≤ K
        omega
  | Mode.ret b, [] => exact trivial
  | Mode.ret b, (u, v, i, j, ph) :: st =>
      obtain ⟨h1, h2, h3⟩ := h
      simp only [rawStep_ret_cons]
      split
      · split
        · exact h3
        · exact wf_advance h1 h3
      · split
        · exact ⟨by simp only [List.length_cons]; omega, by exact ⟨h1, h2, h3⟩⟩
        · exact wf_advance h1 h3
  | Mode.done b, st => exact h

/-! ### Encoding the well-formed states into a fixed finite type -/

/-- Encoded frames. -/
abbrev FrameE (M : NMachine Sigma) (K : ℕ) : Type :=
  Vert M × Vert M × Fin (K + 1) × Fin (cV M) × Bool

/-- Encoded modes. -/
abbrev ModeE (M : NMachine Sigma) (K : ℕ) : Type :=
  (Vert M × Vert M × Fin (K + 1)) ⊕ Bool ⊕ Bool

/-- The finite type into which well-formed raw states are encoded. -/
abbrev RawE (M : NMachine Sigma) (K : ℕ) : Type :=
  ModeE M K × (Fin (K + 1) → Option (FrameE M K))

/-- Encoding of frames. -/
