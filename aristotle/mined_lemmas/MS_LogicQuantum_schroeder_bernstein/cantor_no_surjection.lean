import Mathlib
open Matrix
namespace MS.LogicQuantum


theorem cantor_no_surjection {α : Type*} (f : α → Set α) : ¬ Function.Surjective f :=
  Function.cantor_surjective f

/-- No-cloning: overlap identity forces states orthogonal or identical. -/
