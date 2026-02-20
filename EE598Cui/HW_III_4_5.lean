/- Homework III.4 & III.5 — Non-simple Types and Inference — Zijun Cui -/

import Mathlib

-- II.4 Non-simple Types

-- Ex1: Pair structure with two different types

structure Pair (α : Type*) (β : Type*) where
  fst : α
  snd : β

#check Pair Nat String
#check Pair.mk 666 "world model"

-- Ex2: swap function for Pair

def Pair.swap {α β : Type*} (p : Pair α β) : Pair β α :=
  ⟨p.snd, p.fst⟩

-- the type is {α β : Type*} → Pair α β → Pair β α
#check @Pair.swap

-- Ex3: function f for chooseType

def chooseType : Bool → Type
  | true  => Nat
  | false => String

def f : (b : Bool) → chooseType b
  | true  => (666 : Nat)
  | false => "world model"

#check f true
#check f false
#reduce f true
#reduce f false

-- Ex4: forget function

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons {n} : α → Vec α n → Vec α (n + 1)

def Vec.toList {α : Type} {n : Nat} : Vec α n → List α
  | .nil => []
  | .cons x xs => x :: xs.toList

def forget : (Σ (n : Nat), Vec Nat n) → List Nat
  | ⟨_, v⟩ => v.toList

#eval forget ⟨3, Vec.cons 1 (Vec.cons 2 (Vec.cons 3 Vec.nil))⟩

-- Ex5: length using List.recOn

def length {α} (L : List α) : Nat :=
  List.recOn L 0 (fun h t mt => 1 + mt)

#check List.recOn

#eval length [1, 2, 3, 4, 5]
#eval length ([] : List Nat)

-- Dyadic from previous homework (copied from HW_II.lean)

inductive MyDyadic where
  | zero : MyDyadic
  | add_one : MyDyadic → MyDyadic
  | halve : MyDyadic → MyDyadic
  | negate : MyDyadic → MyDyadic

namespace MyDyadic

def double : MyDyadic → MyDyadic
  | zero => zero
  | add_one x => add_one (add_one (double x))
  | halve x => x
  | negate x => negate (double x)

partial def add : MyDyadic → MyDyadic → MyDyadic
  | zero, y => y
  | x, zero => x
  | add_one x, y => add_one (add x y)
  | halve x, y => halve (add x (double y))
  | negate x, y => negate (add x (negate y))

partial def mul : MyDyadic → MyDyadic → MyDyadic
  | zero, _ => zero
  | add_one x, y => add y (mul x y)
  | halve x, y => halve (mul x y)
  | negate x, y => negate (mul x y)

def to_rat : MyDyadic → ℚ
  | zero => 0
  | add_one x => to_rat x + 1
  | halve x => to_rat x / 2
  | negate x => - to_rat x

-- Ex6: Zero and One instances

instance : Zero MyDyadic where
  zero := MyDyadic.zero

instance : One MyDyadic where
  one := MyDyadic.add_one MyDyadic.zero

def half (d : MyDyadic) : MyDyadic := halve d

#eval to_rat (add_one^[8] 0)
#eval to_rat (double^[8] 1)
#eval to_rat (half^[8] 1)

-- Ex7: HAdd and Add instances

instance : HAdd MyDyadic MyDyadic MyDyadic where
  hAdd := add

instance : Add MyDyadic where
  add := add

def sum (f : ℕ → MyDyadic) (n : ℕ) : MyDyadic :=
  match n with
  | 0 => 0
  | k + 1 => f (k + 1) + sum f k

-- n * 2^(-n)
def n_times_half_n (n : ℕ) : MyDyadic :=
  half^[n] (add_one^[n] 0)

#eval to_rat (sum n_times_half_n 4)

-- Ex8: HMul and Mul instances

instance : HMul MyDyadic MyDyadic MyDyadic where
  hMul := mul

instance : Mul MyDyadic where
  mul := mul

def product (f : ℕ → MyDyadic) (n : ℕ) : MyDyadic :=
  match n with
  | 0 => 1
  | k + 1 => f (k + 1) * product f k

#eval to_rat (product n_times_half_n 4)

end MyDyadic

-- II.5 Inference

-- Ex1: Type Inference for fun x => fun f => f x
-- show it has type A -> (A -> B) -> B

-- derivation:
-- 1) x:A, f:A->B |- f : A->B     by VAR
-- 2) x:A, f:A->B |- x : A        by VAR
-- 3) x:A, f:A->B |- f x : B      by APPL using 1 and 2
-- 4) x:A |- fun f => f x : (A->B)->B    by ABST
-- 5) |- fun x => fun f => f x : A->(A->B)->B   by ABST

#check fun x : _ => fun f : _ → _ => f x

-- Ex2: Inhabitation

def Vec.replicate (n : Nat) (x : α) : Vec α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (Vec.replicate k x)

def g1 : ℕ → Vec ℕ 0 := fun _ => .nil
def g2 : Σ n, Vec ℕ n := ⟨0, .nil⟩
def g3 : Π f : ℕ → ℕ, Σ n, Vec ℕ (f n) := fun f => ⟨0, Vec.replicate (f 0) 0⟩
def g4 : Σ A, Π B, Vec A B := ⟨ℕ, fun n => Vec.replicate n 0⟩
