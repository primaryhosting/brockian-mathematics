/-
First-order instantiation of the abstract second incompleteness theorem
proved in `RequestProject.GoedelSecondIncompleteness`.
-/

import Mathlib
import RequestProject.GoedelSecondIncompleteness

set_option autoImplicit false

namespace Frontier

open FirstOrder Language

variable {L : Language} {T : L.Theory}

/-- Modus ponens for entailment of first-order sentences. -/

theorem boolFramework_hasGoedelSentence :
    ∃ g : boolFramework.Sent, boolFramework.IsGoedelSentence g :=
  ⟨false, rfl, rfl⟩

/-- The theorem applies non-vacuously to `boolFramework`. -/
