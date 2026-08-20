import Mathlib
open Matrix
namespace Frontier.PhysicsQM

def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0,-Complex.I;Complex.I,0]
