/- Homework I.3 — Programming — Zijun Cui -/

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs

def f3 (x : ℕ) : ℕ :=
  let y := x*x
  y+1

#eval f3 4

-- Ex1: abs_diff: absolute value of difference

def abs_diff (a b : ℕ) : ℕ :=
  if a ≥ b then a - b
  else b - a

#eval abs_diff 23 89   -- 66
#eval abs_diff 101 89  -- 12

-- Ex2: apply_twice_when_even

def apply_twice_when_even (f : ℕ → ℕ) (x : ℕ) : ℕ :=
  if x % 2 = 0 then f (f x)
  else f x

#eval apply_twice_when_even (abs_diff 10) 8
#eval apply_twice_when_even (abs_diff 10) 11



-- Ex3: fib using head recursion

def fib : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

#eval fib 0   -- 1
#eval fib 1   -- 1
#eval fib 5   -- 8
#eval fib 10  -- 89


-- Ex4: fib using tail recursion

def fib_helper (n a b : ℕ) : ℕ :=
  match n with
  | 0 => a
  | n + 1 => fib_helper n b (a + b)

def fib_tail (n : ℕ) : ℕ := fib_helper n 1 1

#eval fib_tail 0   -- 1
#eval fib_tail 1   -- 1
#eval fib_tail 5   -- 8
#eval fib_tail 10  -- 89

-- Ex5: mediant: sum of numerators over sum of denominators

def mediant (x y : ℚ) : ℚ :=
  (x.num + y.num) / (x.den + y.den)

#eval mediant (1/2) (1/3)
#eval mediant (2/3) (3/4)

-- Ex6: rep n copies of c

def rep (c : Char) (n : ℕ) : String :=
  match n with
  | 0 => ""
  | n + 1 => String.push (rep c n) c

#eval rep 'c' 5
#eval rep 's' 3
#eval rep 'e' 0

-- Ex7: rev_list - reverse a list

def rev_list {α : Type} (L : List α) : List α :=
  match L with
  | [] => []
  | x :: xs => rev_list xs ++ [x]

#eval rev_list [1, 2, 3, 4, 5]
#eval rev_list ["a", "b", "c"]

-- Ex8: insertion sort

def insert {α : Type} (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insert lt x ys

def insertionSort {α : Type} (lt : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insert lt x (insertionSort lt xs)

def nat_le (a b : ℕ) : Bool := a ≤ b

#eval insertionSort nat_le [3, 1, 4, 1, 5, 9, 2, 6]

-- Ex9: Test with String

def str_cmp (a b : String) : Bool := decide (a ≤ b)

#eval insertionSort str_cmp ["banana", "apple", "cherry", "date"]

#eval insertionSort str_cmp ["zoo", "cat", "dog", "ant"]
