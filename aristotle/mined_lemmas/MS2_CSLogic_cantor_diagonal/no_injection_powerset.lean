import Mathlib
namespace MS2.CSLogic

/-- Cantor's diagonal argument: no map `α → (α → Bool)` is surjective. -/

theorem no_injection_powerset {α : Type*} (f : Set α → α) : ¬ Function.Injective f :=
  Function.cantor_injective f

