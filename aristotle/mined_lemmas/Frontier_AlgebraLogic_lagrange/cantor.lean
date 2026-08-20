import Mathlib
namespace Frontier.AlgebraLogic

theorem cantor {α : Type*} (f : α → Set α) : ¬ Function.Surjective f :=
  Function.cantor_surjective f
