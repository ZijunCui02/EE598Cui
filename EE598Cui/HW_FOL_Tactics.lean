/- Homework III.4 & III.5 — First-Order Logic and Tactics — Zijun Cui -/

import Mathlib

-- III.4 First-Order Logic

inductive Person where | mary | steve | ed | jolin
  deriving DecidableEq

open Person

def on_right (p q : Person) : Prop := match p with
  | mary => q = steve
  | steve => q = ed
  | ed => q = jolin
  | jolin => q = mary

def next_to (p q : Person) := on_right p q ∨ on_right q p

-- Ex1: Define on_left and prove on_left mary jolin

def on_left (p q : Person) : Prop := on_right q p

example : on_left mary jolin := rfl

-- Ex2: Forall elimination

variable (α : Type) (P Q : α → Prop)

example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) :=
  fun h1 h2 x => h1 x (h2 x)

-- Ex3: Exists with on_right

example : ∃ x, on_right mary x := ⟨steve, rfl⟩

example : ∃ x, ¬on_right mary x := ⟨mary, fun h => nomatch h⟩

-- Ex4: PreDyadic exists

inductive PreDyadic where
  | zero    : PreDyadic
  | add_one : PreDyadic → PreDyadic
  | half    : PreDyadic → PreDyadic
  | neg     : PreDyadic → PreDyadic

open PreDyadic

example : ∀ x, ∃ y, y = neg x :=
  fun x => ⟨neg x, rfl⟩

-- Ex5: FOL iff proofs

variable (p q : Type → Prop) (r : Prop)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun h ⟨c, hc⟩ => h c hc)
    (fun h x hpx => h ⟨x, hpx⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨x, hpq⟩ =>
      match hpq with
      | Or.inl hp => Or.inl ⟨x, hp⟩
      | Or.inr hq => Or.inr ⟨x, hq⟩)
    (fun h =>
      match h with
      | Or.inl ⟨x, hp⟩ => ⟨x, Or.inl hp⟩
      | Or.inr ⟨x, hq⟩ => ⟨x, Or.inr hq⟩)

-- Ex6: Person proofs with on_right and next_to

example : ∀ p q : Person, on_right p q → next_to p q :=
  fun _ _ h => Or.inl h

example : ∀ p : Person, ∃ q : Person, next_to p q :=
  fun x => match x with
  | mary => ⟨steve, Or.inl rfl⟩
  | steve => ⟨ed, Or.inl rfl⟩
  | ed => ⟨jolin, Or.inl rfl⟩
  | jolin => ⟨mary, Or.inl rfl⟩

example : ∀ p : Person, ∃ q : Person, ¬next_to p q :=
  fun x => match x with
  | mary => ⟨ed, fun h => h.elim (fun h1 => nomatch h1) (fun h2 => nomatch h2)⟩
  | steve => ⟨jolin, fun h => h.elim (fun h1 => nomatch h1) (fun h2 => nomatch h2)⟩
  | ed => ⟨mary, fun h =>
      match h with
      | Or.inl h1 => nomatch h1
      | Or.inr h2 => nomatch h2⟩
  | jolin => ⟨steve, fun h => h.elim (fun h1 => nomatch h1) (fun h2 => nomatch h2)⟩

-- Ex7: Exists1 definition and elimination

inductive Exists1 {α : Type} (p : α → Prop) : Prop where
  | intro (x : α) (h : p x ∧ ∀ y : α, p y → x = y) : Exists1 p

theorem Exists1.elim {α : Type} {P : α → Prop} {b : Prop}
    (h₁ : Exists1 (fun x => P x)) (h₂ : ∀ (a : α), P a → b) : b :=
  match h₁ with
  | Exists1.intro x ⟨hpx, _⟩ => h₂ x hpx

-- Ex8: Exists1 proofs

example : ∀ x, Exists1 (fun y : Person => x ≠ y ∧ ¬next_to y x) := by
  intro x; cases x with
  | mary =>
    apply Exists1.intro ed
    constructor
    · constructor
      · decide
      · intro h; cases h with | inl h => cases h | inr h => cases h
    · intro y ⟨hne, hnt⟩
      cases y with
      | mary => exact absurd rfl hne
      | steve => exact absurd (Or.inr rfl) hnt
      | ed => rfl
      | jolin => exact absurd (Or.inl rfl) hnt
  | steve =>
    apply Exists1.intro jolin
    constructor
    · constructor
      · decide
      · intro h; cases h with | inl h => cases h | inr h => cases h
    · intro y ⟨hne, hnt⟩
      cases y with
      | mary => exact absurd (Or.inl rfl) hnt
      | steve => exact absurd rfl hne
      | ed => exact absurd (Or.inr rfl) hnt
      | jolin => rfl
  | ed =>
    apply Exists1.intro mary
    constructor
    · constructor
      · decide
      · intro h; cases h with | inl h => cases h | inr h => cases h
    · intro y ⟨hne, hnt⟩
      cases y with
      | mary => rfl
      | steve => exact absurd (Or.inl rfl) hnt
      | ed => exact absurd rfl hne
      | jolin => exact absurd (Or.inr rfl) hnt
  | jolin =>
    apply Exists1.intro steve
    constructor
    · constructor
      · decide
      · intro h; cases h with | inl h => cases h | inr h => cases h
    · intro y ⟨hne, hnt⟩
      cases y with
      | mary => exact absurd (Or.inr rfl) hnt
      | steve => rfl
      | ed => exact absurd (Or.inl rfl) hnt
      | jolin => exact absurd rfl hne

example (α : Type) (P : α → Prop) : Exists1 (fun x => P x) → ¬∀ x, ¬P x :=
  fun h hall => match h with
  | Exists1.intro x ⟨hpx, _⟩ => hall x hpx

example : Exists1 (fun x => x = 0) :=
  Exists1.intro 0 ⟨rfl, fun y hy => hy.symm⟩

example : ¬Exists1 (fun x => x ≠ 0) := by
  intro h
  match h with
  | Exists1.intro x ⟨_, huniq⟩ =>
    have h1 := huniq 1 (by omega)
    have h2 := huniq 2 (by omega)
    omega

-- III.5 Tactics

-- Ex9: Tactic proofs with intro, apply, use

variable (R S : Type → Prop)

example : (∃ x, R x ∧ S x) → ∃ x, S x ∧ R x := by
  intro ⟨x, hp, hq⟩
  apply Exists.intro x
  apply And.intro
  · exact hq
  · exact hp

example : (∃ x, R x ∨ S x) → ∃ x, S x ∨ R x := by
  intro ⟨x, h⟩
  use x
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

-- Ex10: Person next_to with tactics

example : ∀ p : Person, ∃ q : Person, next_to p q := by
  intro x
  cases x with
  | mary => use steve; left; rfl
  | steve => use ed; left; rfl
  | ed => use jolin; left; rfl
  | jolin => use mary; left; rfl

example : ∀ p : Person, ∃ q : Person, ¬next_to p q := by
  intro x
  cases x with
  | mary => use ed; intro h; cases h with | inl h => cases h | inr h => cases h
  | steve => use jolin; intro h; cases h with | inl h => cases h | inr h => cases h
  | ed => use mary; intro h; cases h with | inl h => cases h | inr h => cases h
  | jolin => use steve; intro h; cases h with | inl h => cases h | inr h => cases h

-- Ex11: no_negs for PreDyadic

def PreDyadic.double (x : PreDyadic) : PreDyadic := match x with
  | zero => zero
  | add_one x => add_one (add_one (double x))
  | half x => x
  | neg x => neg (double x)

def PreDyadic.add (x y : PreDyadic) : PreDyadic := match x with
  | zero => y
  | add_one z => (add z y).add_one
  | half z => (add z y.double).half
  | neg z => (add z y.neg).neg

def PreDyadic.mul (x y : PreDyadic) : PreDyadic := match x with
  | zero => zero
  | add_one z => add (mul z y) y
  | half z => (mul z y).half
  | neg z => (mul z y).neg

def no_negs : PreDyadic → Prop
  | .zero => True
  | .add_one x => no_negs x
  | .half x => no_negs x
  | .neg _ => False

theorem no_negs_double (x : PreDyadic) : no_negs x → no_negs x.double := by
  intro h
  induction x with
  | zero => trivial
  | add_one y ih => exact ih h
  | half _ _ => exact h
  | neg _ _ => nomatch h

-- needed as a helper for mul proof below
theorem no_negs_add : (x y : PreDyadic) → no_negs x → no_negs y → no_negs (x.add y) := by
  intro x
  induction x with
  | zero => intro y _ hy; exact hy
  | add_one z ih => intro y hx hy; exact ih y hx hy
  | half z ih => intro y hx hy; exact ih (y.double) hx (no_negs_double y hy)
  | neg _ _ => intro _ hx _; nomatch hx

example (x : PreDyadic) : no_negs x → no_negs (x.double) := no_negs_double x

example (x y : PreDyadic) : no_negs x → no_negs y → no_negs (x.mul y) := by
  intro hx hy
  induction x with
  | zero => trivial
  | add_one z ih => exact no_negs_add _ _ (ih hx) hy
  | half z ih => exact ih hx
  | neg _ _ => nomatch hx

-- Ex12: Choose a tactic — omega
-- omega is a decision procedure for linear arithmetic over ℕ and ℤ.
-- It handles addition, subtraction, multiplication by constants,
-- and automatically resolves systems of linear inequalities.

theorem omega_ex1 : ∀ n : ℕ, 2 * n + 1 > n := by omega

#print omega_ex1
-- omega generates a proof term via Decidable.byContradiction,
-- negating the goal and deriving a contradiction from the resulting
-- system of linear constraints.

theorem omega_ex2 (a b : ℕ) (h : a ≤ b) : a + (b - a) = b := by omega

#print omega_ex2
-- omega handles truncated natural number subtraction (where 3 - 5 = 0)
-- by incorporating the hypothesis a ≤ b into its constraint system,
-- ensuring the subtraction is well-behaved before solving.
