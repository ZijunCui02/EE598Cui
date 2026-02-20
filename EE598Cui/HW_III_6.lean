/- Homework III.6 — Equality — Zijun Cui -/

import Mathlib

-- III.6 Equality

universe u

inductive MyEq {α : Sort u} : α → α → Prop where
  | refl a : MyEq a a

infix:50 " ~ " => MyEq

theorem MyEq.subst {α : Sort u} {P : α → Prop} {a b : α}
    (h₁ : a ~ b) (h₂ : P a) : P b := by
  cases h₁; exact h₂

-- Ex1: MyEq.to_iff

theorem MyEq.to_iff (a b : Prop) : a ~ b → (a ↔ b) := by
  intro h
  cases h
  exact Iff.rfl

-- Ex2: Use ▸

example (P : Type → Prop) : ∀ x y, x = y → P x → ∃ z, P z :=
  fun _ y h hp => ⟨y, h ▸ hp⟩

-- Spin

inductive Spin where | up | dn
open Spin

def Spin.toggle : Spin → Spin
  | up => dn
  | dn => up

postfix:95 " ⁻¹ " => Spin.toggle

@[simp] theorem toggle_up : up⁻¹ = dn := rfl
@[simp] theorem toggle_dn : dn⁻¹ = up := rfl
@[simp] theorem toggle_toggle {x} : x⁻¹⁻¹ = x := by cases x <;> simp

def op (x y : Spin) : Spin := match x, y with
  | up, dn => dn
  | dn, up => dn
  | _, _ => up

infix:75 " o " => op

@[simp] theorem op_up_left {x} : up o x = x := by cases x <;> rfl
@[simp] theorem op_up_right {x} : x o up = x := by cases x <;> rfl
@[simp] theorem op_dn_left {x} : dn o x = x⁻¹ := by cases x <;> rfl
@[simp] theorem op_dn_right {x} : x o dn = x⁻¹ := by cases x <;> rfl

@[simp] theorem toggle_op_left {x y} : (x o y)⁻¹ = x⁻¹ o y := by
  cases x <;> simp

-- Ex3: Spin op proofs

theorem assoc {x y z} : x o (y o z) = (x o y) o z := by
  cases x <;> cases y <;> cases z <;> rfl

theorem com {x y} : x o y = y o x := by
  cases x with
  | up => simp
  | dn => simp

theorem toggle_op_right {x y} : (x o y)⁻¹ = y o x⁻¹ := by
  rw [toggle_op_left, com]

@[simp]
theorem inv_cancel_right {x} : x o x⁻¹ = dn := by
  cases x <;> simp

@[simp]
theorem inv_cancel_left {x} : x⁻¹ o x = dn := by
  cases x <;> simp

-- Ex4: Sum of squares induction

def T (n : Nat) : Nat := match n with
  | Nat.zero => 0
  | Nat.succ x => n * n + T x

example (n : Nat) : 6 * (T n) = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp [T]
  | succ k ih =>
    simp [T]
    linarith

-- Ex5: PreDyadic noConfusion

namespace Eq6

inductive PreDyadic where
  | zero    : PreDyadic
  | add_one : PreDyadic → PreDyadic
  | half    : PreDyadic → PreDyadic
  | neg     : PreDyadic → PreDyadic
open PreDyadic

def PreDyadic.double (x : PreDyadic) : PreDyadic := match x with
  | zero => zero
  | add_one x => add_one (add_one (double x))
  | half x => x
  | neg x => neg (double x)

example (x : PreDyadic) : zero ≠ add_one x := by
  intro h; exact PreDyadic.noConfusion h

example : add_one zero ≠ (add_one (add_one zero)).half := by
  intro h; exact PreDyadic.noConfusion h

-- Ex6: add_one injection

example (x y : PreDyadic) : add_one x = add_one y ↔ x = y := by
  constructor
  · intro h; injection h
  · intro h; rw [h]

-- Ex7: double ∘ half = id

example : PreDyadic.double ∘ PreDyadic.half = id := by
  funext x; rfl

end Eq6

-- Ex8: shift theorems

def shift (k x : ℤ) : ℤ := x + k

@[simp] theorem shift_zero : shift 0 = id := by
  funext x; simp [shift]

@[simp] theorem shift_add {j k} : shift k ∘ shift j = shift (j + k) := by
  funext x; simp [shift, add_assoc]

open Function

example {k} : Bijective (shift k) := by
  rw [bijective_iff_has_inverse]
  use shift (-k)
  constructor
  · simp [leftInverse_iff_comp]
  · simp [rightInverse_iff_comp]

-- Ex9: Spin ≃ Bool

def spin_bool_equiv : Spin ≃ Bool := {
  toFun := fun | up => true | dn => false,
  invFun := fun | true => up | false => dn,
  left_inv := fun x => by cases x <;> rfl,
  right_inv := fun b => by cases b <;> rfl
}
