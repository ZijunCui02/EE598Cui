/- Homework V.1 — Sets — Zijun Cui -/

import Mathlib

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

universe u
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
