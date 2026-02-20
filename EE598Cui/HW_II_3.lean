/- Homework II.3 — Simple Types — Zijun Cui -/

import Mathlib

-- Ex1: Show → is not associative

def ex1a : Type → (Type → Type) := fun _ x => x
def ex1b : (Type → Type) → Type := fun f => f Nat

#check ex1a   -- Type → Type → Type
#check ex1b   -- (Type → Type) → Type

-- Ex2: prepend_label

def prepend_label (s : String) : String := String.append "STRING: " s

#eval prepend_label "hello"
#eval prepend_label "world"

-- Ex3: Context { a : A, b : B, f : A → B } ⊢ f a : B

section
variable (A B : Type)
variable (a : A)
variable (b : B)
variable (f : A → B)

#check f a
end

-- Ex4: Size(M) = 5, M β-reduces to x
-- M = (fun (y : A → A) => x) (fun (z : A) => z)
-- Size(fun y => x) = 1 + 1 = 2
-- Size(fun z => z) = 1 + 1 = 2
-- Size(M) = 1 + 2 + 2 = 5
-- β-reduces to x because y is not used

section
variable (A : Type) (x : A)
#reduce (fun (y : A → A) => x) (fun (z : A) => z)
end

-- Ex5: double for Church numerals

def α' := Type
def CN' := (α' → α') → α' → α'

def cn0 : CN' := fun _ x => x
def cn1 : CN' := fun f x => f x
def cn2 : CN' := fun f x => f (f x)
def cn3 : CN' := fun f x => f (f (f x))

def cn_add : CN' → CN' → CN' := fun m n f x => m f (n f x)
def cn_double : CN' → CN' := fun n => cn_add n n

#reduce (types := true) cn_double cn0
#reduce (types := true) cn_double cn1
#reduce (types := true) cn_double cn3

-- Ex6: Add types to lambda expressions

def ex6a : (Nat → Nat) → Nat → Nat := fun x y => x y
def ex6b : (Nat → Nat → Nat) → Nat → Nat → Nat := fun x y z => x y z
def ex6c : Nat → (Nat → Nat) → Nat := fun x y => y (y (y x))
def ex6d : Nat → (Nat → Nat → Nat) → Nat → Nat := fun x y z => (y x) z

#check ex6a
#check ex6b
#check ex6c
#check ex6d

-- Ex7: Church Pairs
-- A pair (a, b) is encoded as a function that takes a selector f
-- and returns f a b

def CPair := (Nat → Nat → Nat) → Nat

def mk_pair (a b : Nat) : CPair := fun f => f a b
def get_fst (p : CPair) : Nat := p (fun a _ => a)
def get_snd (p : CPair) : Nat := p (fun _ b => b)

#eval get_fst (mk_pair 3 7)    -- 3
#eval get_snd (mk_pair 10 20)  -- 20
