/- Homework III.1 & III.2 Zijun Cui -/

import Mathlib

-- III.1 Propositional Logic

variable (p q r : Prop)

-- Ex1: proven without excluded middle?
-- p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)   provable
-- (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r)   provable
-- ((p → q) → p) → p                 requires excluded middle

theorem dist1 : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) :=
  fun h => h.elim (fun hp => ⟨Or.inl hp, Or.inl hp⟩)
                  (fun hqr => ⟨Or.inr hqr.1, Or.inr hqr.2⟩)

theorem dist2 : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r) :=
  fun ⟨hpq, hpr⟩ =>
    hpq.elim (fun hp => Or.inl hp)
             (fun hq => hpr.elim (fun hp => Or.inl hp)
                                 (fun hr => Or.inr ⟨hq, hr⟩))

theorem peirce_law : ((p → q) → p) → p :=
  fun h => (Classical.em p).elim id (fun hnp => h (fun hp => absurd hp hnp))

#print axioms dist1
#print axioms dist2
#print axioms peirce_law

-- Ex2: Prove ⊢ (p → q) → p → q
-- Goal: ⊢ (p → q) → p → q
--   Apply →-Intro: {p → q} ⊢ p → q
--   Apply →-Intro: {p → q, p} ⊢ q
--   Apply →-Elim:
--     Goal 1: {p → q, p} ⊢ p → q    by Axiom
--     Goal 2: {p → q, p} ⊢ p         by Axiom

-- Ex3: Prove ⊢ p ∧ q → p ∨ q
-- Goal: ⊢ p ∧ q → p ∨ q
--   Apply →-Intro: {p ∧ q} ⊢ p ∨ q
--   Apply ∨-Intro-Left: {p ∧ q} ⊢ p
--   Apply ∧-Elim-Left: {p ∧ q} ⊢ p ∧ q    by Axiom

-- Ex4: Prove ∨ distributing over ∧

-- Direction 1: ⊢ p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)
-- Goal: ⊢ p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)
--   Apply →-Intro: {p ∨ (q ∧ r)} ⊢ (p ∨ q) ∧ (p ∨ r)
--   Apply ∧-Intro:
--     Goal 1: {p ∨ (q ∧ r)} ⊢ p ∨ q
--       Apply ∨-Elim on p ∨ (q ∧ r) (Axiom):
--         case p: →-Intro, ∨-Intro-Left, Axiom
--         case q ∧ r: →-Intro, ∨-Intro-Right, ∧-Elim-Left, Axiom
--     Goal 2: {p ∨ (q ∧ r)} ⊢ p ∨ r
--       same as Goal 1 (case p and case q ∧ r), using ∧-Elim-Right for r

-- Direction 2: ⊢ (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r)
-- Goal: ⊢ (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r)
--   Apply →-Intro: {(p ∨ q) ∧ (p ∨ r)} ⊢ p ∨ (q ∧ r)
--   Apply ∨-Elim on p ∨ q (∧-Elim-Left, Axiom):
--     case p: →-Intro, ∨-Intro-Left, Axiom
--     case q: →-Intro, then need {.., q} ⊢ p ∨ (q ∧ r)
--       Apply ∨-Elim on p ∨ r (∧-Elim-Right, Axiom):
--         case p: →-Intro, ∨-Intro-Left, Axiom
--         case r: →-Intro, ∨-Intro-Right, ∧-Intro (q Axiom, r Axiom)

-- Ex5: Prove ¬¬p ↔ p

-- Direction 1 (p → ¬¬p, constructive):
-- Goal: ⊢ p → ¬¬p, i.e. ⊢ p → (p → False) → False
--   Apply →-Intro twice: {p, p → False} ⊢ False
--   Apply →-Elim:
--     {p, p → False} ⊢ p → False    by Axiom
--     {p, p → False} ⊢ p             by Axiom

-- Direction 2 (¬¬p → p, requires classical logic):
-- Additional inference rule:
--   LEM  ——————————
--         Γ ⊢ φ ∨ ¬φ
--
-- Goal: ⊢ ¬¬p → p
--   Apply →-Intro: {¬¬p} ⊢ p
--   Apply ∨-Elim on p ∨ ¬p:
--     case p: →-Intro, Axiom
--     case ¬p: →-Intro, then need {¬¬p, ¬p} ⊢ p
--       Apply False-Elim: need {¬¬p, ¬p} ⊢ False
--       Apply →-Elim: ¬¬p (Axiom) applied to ¬p (Axiom) gives False

-- III.2 Curry-Howard

variable (P Q : Prop)

-- Ex1: P → P → P → P
-- P → (P → (P → P))

example : P → P → P → P :=
  fun hp _ _ => hp

-- Ex2: (P → Q) → (¬Q → ¬P)

example : (P → Q) → (¬Q → ¬P) :=
  fun hpq hnq hp => nomatch hnq (hpq hp)

-- Ex3: ¬p → (p → q)

example : ¬p → (p → q) :=
  fun hnp hp => nomatch hnp hp

-- Ex4: (∀ x, x > 0) → (∀ y, y > 0)

example : (∀ x, x > 0) → (∀ y, y > 0) :=
  fun h y => h y
