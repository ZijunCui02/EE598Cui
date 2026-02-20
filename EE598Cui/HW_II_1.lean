/- Homework I.2 — Zijun Cui -/

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic

-- Ex14 Define a lambda called h that returns the square of its argument.
-- Evaluate h (h (h 2))

#check fun x => x

#check fun x => x * x

#check fun (x : Nat) => x + 1

#eval (fun (x : Nat) => x + 1) 5

def h (x : Nat) : Nat := x * x

-- fun x => x
