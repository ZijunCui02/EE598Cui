/-
  EE598 Automated Mathematics - Homework I.2
  Student: Cui
  File: HW_I_2.lean

  Instructions:
  - Each exercise is restated as a comment
  - Textual answers are written as comments
  - Lean code should be executable with no errors
  - Use `sorry` for partial credit if stuck
-/

-- Import Mathlib tactics (this may take a while to compile first time)
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith
import Mathlib.Data.Real.Basic

-- ============================================================
-- EXERCISE 1: Basic test (from slide instructions)
-- Verify your environment works correctly
-- ============================================================

#eval 1+2   -- Should output: 3

example (x y z : ℚ)
        (h1 : 2*x < 3*y)
        (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0) : False := by
  linarith

-- ============================================================
-- EXERCISE 2: Figure out how to encode this statement:
-- theorem T₁ : ∀ x : ℝ, 0 ≤ x² := sorry
--
-- Unicode input guide:
--   T₁  → T\_1
--   ∀   → \forall
--   ℝ   → \R
--   ≤   → \le
--   ²   → \^2 or \sup2
-- ============================================================

theorem T₁ : ∀ x : ℝ, 0 ≤ x^2 := by
  intro x
  apply sq_nonneg

-- ============================================================
-- EXERCISE 3: Use #check to determine the types of:
--   (4,5), ℕ × ℕ, and Type
-- ============================================================

#check (4, 5)       -- ℕ × ℕ
#check ℕ × ℕ        -- Type
#check Type         -- Type 1

/-
  Answer:
  - (4, 5) has type ℕ × ℕ (a pair of natural numbers)
  - ℕ × ℕ has type Type (it is a type itself)
  - Type has type Type 1 (the universe hierarchy)
-/

-- ============================================================
-- EXERCISE 4: Redo the proof using `aesop`
-- Original: (p → q) ∧ (q → r) → (p → r)
-- ============================================================

example (p q r : Prop) : (p → q) ∧ (q → r) → (p → r) := by
  aesop

-- ============================================================
-- EXERCISE 5: Write a function `square` that squares every
-- number in a list of natural numbers.
-- Use `remove_zeros` as a template.
-- ============================================================

-- Reference: remove_zeros from the slides
def remove_zeros (L : List ℕ) : List ℕ := match L with
  | [] => List.nil
  | x::Q => if x = 0 then remove_zeros Q else x::(remove_zeros Q)

-- Solution: square function
def square (L : List ℕ) : List ℕ := match L with
  | [] => []
  | x::Q => (x * x) :: square Q

-- Alternative using List.map (more idiomatic)
def square' (L : List ℕ) : List ℕ := L.map (fun x => x * x)

-- Tests
#eval square [1, 2, 3, 4, 5]     -- [1, 4, 9, 16, 25]
#eval square' [1, 2, 3, 4, 5]    -- [1, 4, 9, 16, 25]
#eval square []                  -- []

-- ============================================================
-- EXERCISE 6: Look up List.find? on Loogle
-- Try the examples from the documentation
-- ============================================================

/-
  Loogle search: List.find?
  URL: https://loogle.lean-lang.org/

  List.find? : (a → Bool) → List a → Option a

  Returns the first element of the list satisfying the predicate,
  or none if no such element exists.
-/

#eval [1, 2, 3, 4, 5].find? (· > 3)     -- some 4
#eval [1, 2, 3, 4, 5].find? (· > 10)    -- none
#eval ["hello", "world"].find? (·.length > 4)  -- some "hello"

-- ============================================================
-- END OF HOMEWORK I.2
-- ============================================================
