import Mathlib
open Matrix
namespace MS2.QI3

def CNOT : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0;0,1,0,0;0,0,0,1;0,0,1,0]
