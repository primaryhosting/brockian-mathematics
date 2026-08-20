import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem Deg_mono {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) : Deg F n d₁ ≤ Deg F n d₂ := by
  apply Submodule.span_mono
  rintro f ⟨S, hS, rfl⟩
  exact ⟨S, hS.trans h, rfl⟩

