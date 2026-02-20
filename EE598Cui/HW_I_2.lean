/- Homework I.2 — Zijun Cui -/

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic

-- Ex6 Test eval and a linarith example
#eval 1 + 2

example (x y z : ℚ)
    (h1 : 2 * x < 3 * y)
    (h2 : -4 * x + 2 * z < 0)
    (h3 : 12 * y - 4 * z < 0) : False := by
  linarith

  -- →                   \to
  -- ↔                   \iff
  -- ∀                   \forall
  -- ∃                   \exists
  -- ℕ                   \N
  -- xᵢ                  x\_i

-- Ex9 encode this statement

theorem T₁ : ∀ x : ℝ, 0 ≤ x ^ 2 := sq_nonneg
-- theorem T\_1 : \forall x : \R, \le x ^ 2 := sq_nonneg

-- Ex11: Use #check to determine the types of (4,5), ℕ × ℕ, and Type

#check 1
-- ℕ
#check "1"
-- String
#check ∃ (x : Nat), x < 0
-- Prop
#check fun x => x+1
-- ℕ → ℕ

#check (4, 5)
-- ℕ × ℕ
#check ℕ × ℕ
-- Type
#check Type
-- Type 1

#eval 1+1
-- 2
#eval "hello".append " world"
-- "hello world"
#eval if 2 > 2 then "the universe has a problem" else "everything is ok"
-- "everything is ok"
#eval Nat.Prime 1013
-- true

-- Ex16: aesop: Automated Extensible Search for Obvious Proofs
example (p q r : Prop) : (p → q) ∧ (q → r) → (p → r) := by aesop


def remove_zeros (L : List ℕ) : List ℕ := match L with
  | [] => List.nil
  | x::Q => if x = 0 then remove_zeros Q else x::(remove_zeros Q)

#check remove_zeros

#eval remove_zeros [1,2,3,0,5,0,0]     -- [1,2,3,5]

-- Ex18: Write a function square that squares every number in a list of natural numbers.
-- Use remove_zeros as a template. Test your code using #eval.
def square (L : List ℕ) : List ℕ := match L with
  | [] => []
  | x :: xs => (x * x) :: square xs

#eval square [1, 2, 3, 4, 5]

-- Ex20: Look up List.find? on Loogle and try the examples.

#eval [7, 6, 5, 8, 1, 2, 6].find? (· < 5) = some 1
#eval [7, 6, 5, 8, 1, 2, 6].find? (· < 1) = none

-- List.find? returns the first element in the list satisfying the predicate
