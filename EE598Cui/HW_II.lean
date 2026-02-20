/- Homework II — Datatypes, Simple Types, Universes — Zijun Cui -/

import Mathlib

-- I.4 Datatypes

-- Ex1: complex number

structure PolarComplex where
  mag : NNReal
  arg : ℝ

-- Ex2: Define or for TriBool

inductive TriBool where
  | T : TriBool
  | F : TriBool
  | U : TriBool

open TriBool

def TriBool.or (A B : TriBool) : TriBool :=
  match A, B with
  | T, _ => T
  | _, T => T
  | F, F => F
  | _, _ => U

-- Ex3: Define reciprocal

def reciprocal (x : ℚ) : Option ℚ :=
  if x = 0 then none else some (1 / x)

#eval reciprocal 0
#eval reciprocal 2

-- Ex4: BTree swap

inductive BTree (A : Type) where
  | leaf : A → BTree A
  | node : A → BTree A → BTree A → BTree A

namespace BTree
#check leaf

def swap {A : Type} (T : BTree A) : BTree A :=
  match T with
  | leaf a => leaf a
  | node a left right => node a (swap right) (swap left)

def my_tree := node 1 (leaf 2) (node 3 (leaf 4) (leaf 5))

#eval swap my_tree

end BTree

-- Ex5: Expr.CountAdds

mutual
  inductive Term
  | var : String → Term
  | num : ℕ → Term
  | paren : Expr → Term

  inductive Expr
  | neg : Term → Expr
  | add : Term → Term → Expr
  | mul : Term → Term → Expr
end

mutual
  def Term.CountAdds (t : Term) : ℕ :=
    match t with
    | Term.var _ => 0
    | Term.num _ => 0
    | Term.paren e => Expr.CountAdds e

  def Expr.CountAdds (e : Expr) : ℕ :=
    match e with
    | Expr.neg t => Term.CountAdds t
    | Expr.add t1 t2 => 1 + Term.CountAdds t1 + Term.CountAdds t2
    | Expr.mul t1 t2 => Term.CountAdds t1 + Term.CountAdds t2
end

-- Ex6: Define 3DVector

structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

-- Ex7: Cross product

def cross (a b : Vec3) : Vec3 :=
  { x := a.y * b.z - a.z * b.y,
    y := a.z * b.x - a.x * b.z,
    z := a.x * b.y - a.y * b.x }

-- Ex8: Cross product with ℝ × ℝ × ℝ

def cross' (a b : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1,
   a.2.2 * b.1 - a.1 * b.2.2,
   a.1 * b.2.1 - a.2.1 * b.1)

-- Ex9: Shape area and perimeter

def Shape :=  ℚ ⊕ (ℚ × ℚ)
def pi :ℚ := 22/7
def area (s : Shape) : ℚ :=
  match s with
  | Sum.inl r => pi * r * r
  | Sum.inr (x, y) => x * y

def perimeter (s : Shape) : ℚ :=
  match s with
  | Sum.inl r => 2 * pi * r
  | Sum.inr (x, y) => 2 * (x + y)

#eval area (Sum.inl 7)
#eval area (Sum.inr (3, 4))
#eval perimeter (Sum.inl 7)
#eval perimeter (Sum.inr (3, 4))

-- Ex10: MyTree

inductive MyTree (A : Type) where
  | node : A → List (MyTree A) → MyTree A

namespace MyTree

-- Ex11: map for MyTree

def map {A B : Type} (f : A → B) : MyTree A → MyTree B
  | node a children => node (f a) (children.map (map f))

def example_tree : MyTree ℕ := node 1 [node 2 [], node 3 [node 4 []]]

#eval map (· * 2) example_tree

-- Ex12: Convert BTree to MyTree

def fromBTree {A : Type} : BTree A → MyTree A
  | BTree.leaf a => node a []
  | BTree.node a left right => node a [fromBTree left, fromBTree right]

#eval fromBTree BTree.my_tree

end MyTree

-- Ex13: Dyadic Rationals

inductive MyDyadic where
  | zero : MyDyadic
  | add_one : MyDyadic → MyDyadic
  | halve : MyDyadic → MyDyadic
  | negate : MyDyadic → MyDyadic

namespace MyDyadic

-- a. double
def double : MyDyadic → MyDyadic
  | zero => zero
  | add_one x => add_one (add_one (double x))
  | halve x => x
  | negate x => negate (double x)

-- b. add
partial def add : MyDyadic → MyDyadic → MyDyadic
  | zero, y => y
  | x, zero => x
  | add_one x, y => add_one (add x y)
  | halve x, y => halve (add x (double y))
  | negate x, y => negate (add x (negate y))

-- c. mul
partial def mul : MyDyadic → MyDyadic → MyDyadic
  | zero, _ => zero
  | add_one x, y => add y (mul x y)
  | halve x, y => halve (mul x y)
  | negate x, y => negate (mul x y)

-- d. to_rat
def to_rat : MyDyadic → ℚ
  | zero => 0
  | add_one x => to_rat x + 1
  | halve x => to_rat x / 2
  | negate x => - to_rat x

-- e. 5/8 and -7/32
def five : MyDyadic := add_one (add_one (add_one (add_one (add_one zero))))
def seven : MyDyadic := add_one (add_one (add_one (add_one (add_one (add_one (add_one zero))))))

def five_eighths : MyDyadic := halve (halve (halve five))
def neg_7_32 : MyDyadic := negate (halve (halve (halve (halve (halve seven)))))

#eval to_rat five_eighths
#eval to_rat neg_7_32
#eval to_rat (add five_eighths neg_7_32)
#eval to_rat (mul five_eighths five_eighths)

end MyDyadic

-- f. Are Dyadics unique?
-- No. The same number can have multiple representations:
-- for example 1 = add_one zero = halve (double (add_one zero))


-- II.1 Foundations

-- Ex2: Define lambda h that returns square

def h (x : ℕ) : ℕ := x * x

#eval h 2

-- Ex3: Evaluate h (h (h 2))

#eval h (h (h 2))

-- Ex4: Define Ω in Lean

#check fun x => x x

-- Expected a function because this term is being applied to the argument
-- I think x can not be Type -> Type and also be Type at the same time.

-- Ex5: Watch the video

-- Question 1: Why do AI models need Lean to do math?
-- AI hallucinates. Lean catches wrong proofs. AI suggests steps, Lean checks if they're actually correct.

-- question 2: How can mathematicians collaborate on proofs without trusting each other's work?
-- When someone contributes a proof via lean, it verify the proof itself. This shifts trust from people to mathematical verification.

-- question 3: Can language models replace human mathematicians?
-- No? Language models hallucinate confidently. Lean catches these errors by checking proofs formally.

-- II.2 Universes

-- Ex1: Type of Type u ⊕ Type v

universe u v
#check Type u
#check Type v
#check Type u ⊕ Type v

-- Ex2: TypeList

def TypeList := List Type

def A1 : TypeList := []
-- this is ok becaue it is empty
def A2 : TypeList := [TypeList]
#check TypeList
-- this is error, because TypeList is Type 1, so it can only hold Type 0
def A3 : TypeList := [ℕ,ℚ]
-- this is ok, because ℕ and ℚ are Type 0
def A4: TypeList := [ℕ,ℕ×Type]
#check ℕ
#check Type
#check ℕ ×Type
-- this is error, because Type is Type 1, so it can not be in TypeList
def A5 : TypeList := [ℕ,List ℕ]
#check List ℕ
-- this is ok, because they are all Type 0
def A6 : TypeList := [ℕ,ℕ×Prop]
#check ℕ × Prop
-- this is ok because they are all Type 0
def A7 : TypeList := [ℕ,A]
#check A
-- this is error because A is not defined

-- Ex3: TypeList with universe variable

def TypeList' := List (Type u)

def B1 : TypeList'.{0} := []
-- is ok because it is empty
def B2 : TypeList'.{1} := [TypeList'.{0}]
-- is ok because TypeList'.{0} is Type 1, so it can be in TypeList'.{1}
def B3 : TypeList'.{0} := [ℕ, ℚ]
-- is ok because ℕ and ℚ are Type 0

-- Ex4: Why doesn't this type check? How to fix?

-- This does NOT work:
#check_failure fun (n : ℕ) => if n = 0 then Type 0 else Type 1

-- Reason:
--   Type 0 : Type 1
--   Type 1 : Type 2
--   if-then-else needs both branches to have SAME type

-- Workaround: return types that are all in Type 0? I don't know a better way

def f2 (n : ℕ) : Type := if n = 0 then ℕ else ℚ

#check f2 0
#check f2 1
