/- Homework IV.3 — Relations — Zijun Cui -/

import Mathlib

namespace HW

universe u
variable {α : Sort u}

def te (σ₁ σ₂ : ℕ → α) : Prop := ∃ m, ∀ n > m, σ₁ n = σ₂ n

def Refl (R : α → α → Prop) := ∀ x, R x x
def Symm (R : α → α → Prop) := ∀ x y, R x y → R y x
def AntiSymm (R : α → α → Prop) := ∀ x y, R x y → R y x → x = y
def Trans (R : α → α → Prop) := ∀ x y z, R x y → R y z → R x z

-- Ex1: Remaining symmetry examples

example : Symm Or := fun _ _ h => h.symm

example : ¬Symm (Set.Subset (α := ℕ)) := by
  intro h
  have h1 : ({1} : Set ℕ) ⊆ {1, 2} := by simp
  have h2 := h _ _ h1
  have : (2 : ℕ) ∈ ({1} : Set ℕ) := h2 (by simp)
  simp at this

example : Symm (Eq (α := ℕ)) := fun _ _ h => h.symm

-- Ex2: Remaining antisymmetry examples

example : AntiSymm Nat.le := fun _ _ h1 h2 => Nat.le_antisymm h1 h2

example : AntiSymm And := by
  intro x y ⟨hx, hy⟩ _
  exact propext ⟨fun _ => hy, fun _ => hx⟩

example : ¬AntiSymm Or := by
  intro h
  have := h True False (.inl trivial) (.inr trivial)
  simp at this

example : AntiSymm (Eq (α := ℕ)) := fun _ _ h _ => h

-- Ex3: Remaining transitivity examples

example : Trans Nat.le := fun _ _ _ h1 h2 => Nat.le_trans h1 h2

example : Trans (Eq (α := ℕ)) := fun _ _ _ h1 h2 => h1.trans h2

example : Trans (te (α := α)) := by
  intro x y z ⟨m₁, h₁⟩ ⟨m₂, h₂⟩
  exact ⟨m₁ ⊔ m₂, fun n hn => by rw [h₁ n (by omega), h₂ n (by omega)]⟩

-- Ex4: Relation definitions are equivalent

def relation_defs_equiv {α : Type u} : (α → α → Prop) ≃ Set (α × α) := {
  toFun R := { p | R p.1 p.2 },
  invFun S a b := (a, b) ∈ S,
  left_inv := fun _ => rfl,
  right_inv := fun _ => by ext ⟨_, _⟩; rfl
}

-- Closures from lecture

inductive ReflC (R : α → α → Prop) : α → α → Prop where
  | base {x y} : R x y → ReflC R x y
  | refl {x} : ReflC R x x

inductive SymmC (R : α → α → Prop) : α → α → Prop where
  | base {x y} : R x y → SymmC R x y
  | symm {x y} : R x y → SymmC R y x

inductive TransC (R : α → α → Prop) : α → α → Prop where
  | base {x y} : R x y → TransC R x y
  | trans {x y z} : R x y → TransC R y z → TransC R x z

-- Ex5: Symmetric closure of a symmetric relation is the relation itself

example (R : α → α → Prop)
  : Symm R → ∀ x y, R x y ↔ (SymmC R) x y := by
  intro hs x y
  constructor
  · exact SymmC.base
  · intro h
    cases h with
    | base h => exact h
    | symm h => exact hs _ _ h

-- Ex6: ReflC (TransC R) ↔ TransC (ReflC R)

example (R : α → α → Prop) : ∀ x y,
  ReflC (TransC R) x y ↔ TransC (ReflC R) x y := by
  intro x y
  constructor
  · intro h
    cases h with
    | refl => exact TransC.base ReflC.refl
    | base h =>
      induction h with
      | base h => exact TransC.base (ReflC.base h)
      | trans h _ ih => exact TransC.trans (ReflC.base h) ih
  · intro h
    induction h with
    | base h =>
      cases h with
      | base h => exact ReflC.base (TransC.base h)
      | refl => exact ReflC.refl
    | trans h _ ih =>
      cases h with
      | base h =>
        cases ih with
        | refl => exact ReflC.base (TransC.base h)
        | base ih => exact ReflC.base (TransC.trans h ih)
      | refl => exact ih

-- Ex7: Subsequence order

def subseq {α : Type u} (σ τ : ℕ → α) :=
  ∃ f, StrictMono f ∧ σ = τ ∘ f

theorem subseq_refl {α : Type u} : Refl (subseq (α := α)) :=
  fun _ => ⟨id, strictMono_id, rfl⟩

theorem subseq_trans {α : Type u} : Trans (subseq (α := α)) :=
  fun _ _ _ ⟨f, hf, hσ⟩ ⟨g, hg, hτ⟩ => ⟨g ∘ f, hg.comp hf, by rw [hσ, hτ]; rfl⟩

theorem subseq_not_antisymm : ¬AntiSymm (subseq (α := ℕ)) := by
  intro h
  let σ : ℕ → ℕ := fun n => n % 2
  let τ : ℕ → ℕ := fun n => (n + 1) % 2
  have hm : StrictMono (fun n : ℕ => n + 1) := fun _ _ hab => Nat.add_lt_add_right hab 1
  have hστ : subseq σ τ := ⟨fun n => n + 1, hm, by funext n; simp only [σ, τ, Function.comp]; omega⟩
  have hτσ : subseq τ σ := ⟨fun n => n + 1, hm, by funext n; simp only [σ, τ, Function.comp]⟩
  have heq := h σ τ hστ hτσ
  have : σ 0 = τ 0 := congr_fun heq 0
  simp only [σ, τ] at this; omega

-- Tail equivalence from lecture

instance te_equiv {α : Type u} : Equivalence (te (α := α)) := {
  refl x := ⟨0, fun _ _ => rfl⟩,
  symm := fun ⟨m, h⟩ => ⟨m, fun n hn => (h n hn).symm⟩,
  trans := fun ⟨m₁, h₁⟩ ⟨m₂, h₂⟩ =>
    ⟨m₁ ⊔ m₂, fun n hn => by rw [h₁ n (by omega), h₂ n (by omega)]⟩
}

instance te_setoid {α : Type u} : Setoid (ℕ → α) := ⟨te, te_equiv⟩

def Germ (α : Type u) := Quotient (te_setoid (α := α))

namespace Germ

instance inst_zero {α : Type u} [Zero α] : Zero (Germ α) := ⟨⟦fun _ => 0⟧⟩

-- Ex8: Lift shift to Germ

def pre_shift {α : Type u} (σ : ℕ → α) : Germ α := ⟦fun n => σ (n + 1)⟧

theorem pre_shift_respects {α : Type u}
  : ∀ (a b : ℕ → α), a ≈ b → pre_shift a = pre_shift b := by
  intro a b ⟨m, hm⟩
  apply Quotient.sound
  exact ⟨m, fun n hn => hm (n + 1) (by omega)⟩

def shift {α : Type u} (σ : Germ α) : Germ α :=
  Quotient.lift pre_shift pre_shift_respects σ

-- Ex9: shift 0 = 0

example : shift (0 : Germ ℤ) = 0 := by
  apply Quotient.sound
  exact ⟨0, fun _ _ => rfl⟩

-- Ex10: Non-equivalence-preserving function

def my_func (σ : ℕ → ℕ) : ℕ → ℕ := fun _ => σ 0
def σ₁ : ℕ → ℕ := fun _ => 0
def σ₂ : ℕ → ℕ := fun n => if n = 0 then 1 else 0

example : σ₁ ≈ σ₂ ∧ ¬my_func σ₁ ≈ my_func σ₂ := by
  refine ⟨⟨0, fun n hn => ?_⟩, fun ⟨m, hm⟩ => ?_⟩
  · simp only [σ₁, σ₂, if_neg (by omega : ¬n = 0)]
  · have := hm (m + 1) (by omega)
    simp [my_func, σ₁, σ₂] at this

end Germ
end HW
