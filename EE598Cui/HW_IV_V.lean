/- Homework IV.1 & V.1 — Algebra & Sets — Zijun Cui -/

import Mathlib

-- IV.1 Algebra

namespace Temp

universe u

-- Group definition (from lecture)

class Group (G : Type u) where
  op : G → G → G
  e : G
  inv : G → G
  assoc {a b c} : op (op a b) c = op a (op b c)
  id_left {a} : op e a = a
  inv_left {a} : op (inv a) a = e

class CommGroup (G : Type u) extends Group G where
  comm {a b} : op a b = op b a

scoped infixl:60 " + " => Group.op
scoped prefix:95 "-" => Group.inv

open Group CommGroup

variable {G : Type u} [Group G] {a b c : G}

-- Derived identities needed for exercises

theorem Group.cancel_left : a + b = a + c → b = c := by
  intro h
  apply congrArg (fun t => -a + t) at h
  simp only [←assoc, inv_left, id_left] at h
  exact h

theorem Group.id_right : a + e = a := by
  apply cancel_left (a := -a)
  simp [←assoc, id_left, inv_left]

theorem Group.inv_right : a + (-a) = e := by
  apply cancel_left (a := -a)
  simp [←assoc, inv_left, id_left, id_right]

-- Ex1: identity is unique

theorem Group.id_unique {e' : G} : (∀ a, e'+ a = a) → e = e' := by
  intro h
  have h1 := h e
  rw [id_right] at h1
  exact h1.symm

-- Ex2: inverse is unique

theorem Group.inv_unique : b + a = e → c + a = e → b = c := by
  intro hb hc
  have h : b + a = c + a := by rw [hb, hc]
  apply congrArg (· + (-a)) at h
  simp only [assoc, inv_right, id_right] at h
  exact h

-- Spin

inductive Spin where | up | dn
open Spin

def Spin.toggle : Spin → Spin
  | up => dn
  | dn => up

def sop (x y : Spin) : Spin := match x, y with
  | up, dn => dn
  | dn, up => dn
  | _, _ => up

instance Spin.inst_comm_group : CommGroup Spin := {
  op := sop,
  e := up,
  inv := id,
  assoc {a b c} := by cases a <;> cases b <;> cases c <;> rfl,
  id_left {a}   := by cases a <;> rfl
  inv_left {a}  := by cases a <;> rfl
  comm {a b}    := by cases a <;> cases b <;> rfl
}

-- Ex3: product of two groups is a group

instance Group.prod {G H : Type u} [Group G] [Group H] : Group (G × H) := {
  op x y := (x.1 + y.1, x.2 + y.2),
  e := (e, e),
  inv x := (-x.1, -x.2),
  id_left {x} := by simp [id_left]
  inv_left := by simp [inv_left],
  assoc := by simp [assoc]
}

-- Ex4: Spin product group

example : (e : Spin × Spin) = (up, up) := rfl
example : (-(up, up) : Spin × Spin) = (up, up) := rfl
example (x : Spin × Spin) : -x + x = (up, up) := by
  cases x with | mk a b => cases a <;> cases b <;> rfl

-- Ring theory

class Monoid (M : Type u) where
  mul : M → M → M
  one : M
  mul_assoc {a b c : M} : mul (mul a b) c = mul a (mul b c)
  mul_id_left {a : M} : mul one a = a
  mul_id_right {a : M} : mul a one = a

class Ring (R : Type u)
  extends CommGroup R, Monoid R where
  l_distrib {x y z : R} : mul x (op y z) = op (mul x y) (mul x z)
  r_distrib {x y z : R} : mul (op y z) x = op (mul y x) (mul z x)

class CommRing (R : Type u)
  extends Ring R where
  mulcomm {x y : R} : mul x y = mul y x

variable {R : Type u} [CommRing R]

scoped infixl:80 " * " => Monoid.mul

open Monoid Ring CommRing

variable {x y z : R}

theorem Ring.add_left (h : y = z) (x : R) : x + y = x + z := by rw [h]
theorem Ring.mul_left (h : y = z) (x : R) : x * y = x * z := by rw [h]

theorem mul_zero : x * (e : R) = e := by
  have h0 := l_distrib (x := x) (y := e) (z := e)
  have h := Ring.add_left h0 (-(x * e))
  rw [id_left] at h
  rw [inv_left] at h
  rw [←assoc] at h
  rw [inv_left] at h
  rw [id_left] at h
  exact h.symm

-- Ex5: x*(-y) = -(x*y)

theorem factor_mul_inv_right : x * (-y) = -(x * y) := by
  have h1 : x * y + x * (-y) = (e : R) := by
    rw [←l_distrib, inv_right, mul_zero]
  have h2 := Ring.add_left h1 (-(x * y))
  rw [←assoc, inv_left, id_left, id_right] at h2
  exact h2

-- Spin monoid and ring

def Spin.mul (a b : Spin) : Spin :=
  match a, b with
  | dn, dn => dn
  | _, _ => up

instance Spin.inst_monoid : Monoid Spin := {
  one := dn,
  mul := Spin.mul
  mul_assoc {x y z} := by cases x <;> cases y <;> cases z <;> rfl
  mul_id_left {x}   := by cases x <;> rfl
  mul_id_right {x}  := by cases x <;> rfl
}

instance Spin.inst_ring : Ring Spin := {
  l_distrib {x y z} := by cases x <;> cases y <;> cases z <;> rfl
  r_distrib {x y z} := by cases x <;> cases y <;> cases z <;> rfl
}

-- Ex6: Spin ring identity

example (x y : Spin) : x * y + x = x * (y + dn) := by
  cases x <;> cases y <;> rfl

-- Sequence group/monoid (from lecture)

instance Seq.inst_group {R : Type u} [Group R] : Group (ℕ → R) := {
  op f g n      := f n + g n,
  e n           := e,
  inv f n       := -f n,
  assoc {f g h} := by funext n; exact assoc,
  id_left {f}   := by funext n; exact id_left,
  inv_left {f}  := by funext n; exact inv_left
}

instance Seq.inst_comm_group {R : Type u} [CommGroup R] : CommGroup (ℕ → R) := {
  comm {f g} := by funext n; exact comm
}

instance Seq.inst_monoid {R : Type u} [Monoid R] : Monoid (ℕ → R) := {
  mul f g n := f n * g n,
  one n := one,
  mul_assoc {f g h} := by funext n; exact Monoid.mul_assoc,
  mul_id_left {f}   := by funext n; exact mul_id_left
  mul_id_right {f}  := by funext n; exact mul_id_right
}

-- Ex7: ℕ → R is a Ring and CommRing

instance Seq.inst_ring {R : Type u} [Ring R] : Ring (ℕ → R) := {
  l_distrib {f g h} := by funext n; exact l_distrib,
  r_distrib {f g h} := by funext n; exact r_distrib
}

instance Seq.inst_comm_ring {R : Type u} [CommRing R] : CommRing (ℕ → R) := {
  mulcomm {f g} := by funext n; exact mulcomm
}

-- Ex8: Principal Ideal (optional)

structure Ideal (R : Type u) [CommRing R] where
  I : R → Prop
  has_zero : I e
  closed {x y : R} : I x → I y → I (-x + y)
  absorb {r x : R} : I x → I (r * x) ∧ I (x * r)

def PrincipalIdeal {R : Type u} [CommRing R] (x : R) : Ideal R := {
  I y := ∃ r : R, y = x * r,
  has_zero := ⟨e, (mul_zero).symm⟩,
  closed := by
    intro a b ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨-r + s, by rw [hr, hs, l_distrib, factor_mul_inv_right]⟩
  absorb := by
    intro r a ⟨s, hs⟩
    constructor
    · exact ⟨r * s, by rw [hs, ←Monoid.mul_assoc, mulcomm (x := r), Monoid.mul_assoc]⟩
    · exact ⟨s * r, by rw [hs, Monoid.mul_assoc]⟩
}

-- Field

class Field (F : Type u) extends CommRing F, Nontrivial F where
  minv : F → F
  minv_zero : minv e = e
  mul_inv_prop {x : F} : x ≠ e → mul x (minv x) = one

open Field

variable {F : Type u} [Field F]

scoped postfix:95 "⁻¹" => Field.minv

-- Ex9: (one)⁻¹ = one

theorem one_inv : (one : F)⁻¹ = one := by
  have h : (one : F) ≠ e := by
    intro h
    obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial F).exists_pair_ne
    have hx : x = e := by
      calc x = x * one := by rw [mul_id_right]
        _ = x * e := by rw [h]
        _ = e := by rw [mul_zero]
    have hy : y = e := by
      calc y = y * one := by rw [mul_id_right]
        _ = y * e := by rw [h]
        _ = e := by rw [mul_zero]
    exact hxy (hx.trans hy.symm)
  have h1 := mul_inv_prop h
  rw [mul_id_left] at h1
  exact h1

-- Ex10: ℤ as a CommRing (using our definitions)

instance Int.inst_group : Group ℤ := {
  op := (· + ·),
  e := 0,
  inv := fun x => -x,
  assoc {a b c} := add_assoc a b c,
  id_left {a} := zero_add a,
  inv_left {a} := neg_add_cancel a
}

instance Int.inst_comm_group : CommGroup ℤ := {
  comm {a b} := add_comm a b
}

instance Int.inst_monoid : Monoid ℤ := {
  mul := (· * ·),
  one := 1,
  mul_assoc {a b c} := _root_.mul_assoc a b c,
  mul_id_left {a} := one_mul a
  mul_id_right {a} := mul_one a
}

instance Int.inst_ring : Ring ℤ := {
  l_distrib {x y z} := mul_add x y z
  r_distrib {x y z} := add_mul y z x
}

instance Int.inst_comm_ring : CommRing ℤ := {
  mulcomm {x y} := mul_comm x y
}

end Temp

-- V.1 Sets

-- Ex1: Evens addition and associativity

def Evens := { n : ℕ // ∃ k, n = 2 * k }

def Evens.add (x y : Evens) : Evens :=
  ⟨x.val + y.val, by
    obtain ⟨k, hk⟩ := x.property
    obtain ⟨j, hj⟩ := y.property
    exact ⟨k + j, by omega⟩⟩

def Evens.add_assoc {x y z : Evens}
  : Evens.add x (Evens.add y z) = Evens.add (Evens.add x y) z := by
  apply Subtype.ext; simp [Evens.add]; omega

-- Ex2: Subset proofs

variable (α β : Type u) {A B C : Set α} {D E : Set β}

example : A ⊆ C → B ⊆ C → A ∪ B ⊆ C := by
  intro hac hbc x hx
  cases hx with
  | inl h => exact hac h
  | inr h => exact hbc h

example : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro hab hbc x hx
  exact hbc (hab hx)

-- Ex3: Image distributes over union

example {f : α → β} : f '' (A ∪ B) = f '' A ∪ f '' B := by
  ext x; constructor
  · rintro ⟨y, hy | hy, rfl⟩
    · left; exact ⟨y, hy, rfl⟩
    · right; exact ⟨y, hy, rfl⟩
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨y, Or.inl hy, rfl⟩
    · exact ⟨y, Or.inr hy, rfl⟩

-- Ex4: Preimage distributes over intersection

example {f : α → β} : f ⁻¹' (D ∩ E) = f ⁻¹' D ∩ f ⁻¹' E := by
  ext x; exact Iff.rfl

-- Ex5: Properties of Fin

example : Fin 0 → False := Fin.elim0

example (x : Fin 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp

example (n : ℕ) (x y : Fin n) : x = y ↔ x.val = y.val := Fin.ext_iff

-- Ex6: Fin n ≃ { x : ℕ | x < n }

def equiv_subtype {n : ℕ} : Fin n ≃ { x : ℕ | x < n } := {
  toFun x := ⟨x.val, x.isLt⟩,
  invFun x := ⟨x.val, x.property⟩,
  left_inv := fun _ => by simp,
  right_inv := fun _ => by simp
}

-- Ex7: Fin n ≃ Fin m → n = m

theorem equiv_same_size {n m : ℕ} (eq : Fin n ≃ Fin m) : n = m := by
  have := Fintype.card_congr eq
  simp only [Fintype.card_fin] at this
  exact this
