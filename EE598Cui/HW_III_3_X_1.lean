/- Homework III.3 & X.1 — Connectives and Projects — Zijun Cui -/

import Mathlib

-- III.3 Connectives

variable (p q r : Prop)

-- Ex1: And associativity

example : p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
  fun ⟨hp, hqr⟩ => ⟨⟨hp, hqr.1⟩, hqr.2⟩

-- Ex2: Iff is both directions of implies

example (p q : Prop) : (p ↔ q) ↔ (p → q) ∧ (q → p) :=
  ⟨fun h => ⟨h.mp, h.mpr⟩, fun h => ⟨h.1, h.2⟩⟩

-- Ex3: Propositional logic identities

example : p ∨ q ↔ q ∨ p :=
  ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  ⟨fun h => h.elim (fun hpq => hpq.elim Or.inl (fun hq => Or.inr (Or.inl hq)))
                    (fun hr => Or.inr (Or.inr hr)),
   fun h => h.elim (fun hp => Or.inl (Or.inl hp))
                    (fun hqr => hqr.elim (fun hq => Or.inl (Or.inr hq)) Or.inr)⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩,
   fun ⟨hnp, hnq⟩ hpq =>
     match hpq with
     | Or.inl hp => hnp hp
     | Or.inr hq => hnq hq⟩

example : ¬(p ∧ ¬p) :=
  fun ⟨hp, hnp⟩ => hnp hp

example : (¬p ∨ q) → (p → q) :=
  fun h hp => h.elim (fun hnp => nomatch hnp hp) (fun hq => hq)

example : p ∨ False ↔ p :=
  ⟨fun h => h.elim (fun hp => hp) (fun hf => nomatch hf), fun hp => Or.inl hp⟩

example : p ∧ False ↔ False :=
  ⟨fun ⟨_, hf⟩ => hf, fun hf => nomatch hf⟩

-- Ex4: Requires excluded middle

example : (p → q) → (¬p ∨ q) :=
  fun hpq => (Classical.em p).elim (fun hp => Or.inr (hpq hp)) Or.inl

-- Ex5: Nor definition and elimination rules

inductive Nor (p q : Prop) : Prop where
  | intro : ¬p → ¬q → Nor p q

def Nor.elim_left {p q : Prop} (hnpq : Nor p q) : ¬p :=
  match hnpq with
  | Nor.intro hnp _ => hnp

def Nor.elim_right {p q : Prop} (hnpq : Nor p q) : ¬q :=
  match hnpq with
  | Nor.intro _ hnq => hnq

-- Ex6: Nor proofs

example : ¬p → (Nor p p) :=
  fun hnp => Nor.intro hnp hnp

example : (Nor p q) → ¬(p ∨ q) :=
  fun hnpq hpq => hpq.elim hnpq.elim_left hnpq.elim_right

example : ¬(p ∨ q) → (Nor p q) :=
  fun h => Nor.intro (fun hp => h (Or.inl hp)) (fun hq => h (Or.inr hq))

-- X.1 Projects

-- Ex1: Project exploration
--
-- Prompts used (conversation with Copilot, exploring several topics):
--
-- Phase 1: Understanding the project and brainstorming
--
-- 1. Q: I'm taking EE598 (Automated Math) and need to do a 5-week course
--       project in Lean 4. What does a project like this actually involve?
--       I've never done formal verification beyond homework exercises.
--    A: The project is pure math formalization — you pick a piece of math,
--       define it in Lean 4 (types, functions, structures), then write
--       machine-checked proofs of its properties. No data, no training,
--       no simulation. Just definitions and proofs. The output is a Lean
--       file where every theorem compiles without sorry.
--
-- 2. Q: Can you brainstorm some project ideas for an EE grad student?
--       I want something that connects to electrical engineering, not
--       pure math for its own sake.
--    A: Some options: (1) digital circuit verification — prove adder or
--       ALU correctness, (2) control system stability — formalize BIBO or
--       Lyapunov, (3) signal processing — prove DFT/convolution properties,
--       (4) error-correcting codes — formalize Hamming codes over GF(2),
--       (5) communication theory — Shannon's channel capacity bounds.
--
-- 3. Q: I'm zijuncui.com — can you look at my research background and
--       suggest topics that actually connect to what I work on?
--    A: Your research is on multimodal spatial understanding, audio-visual
--       LLMs (SAVVY, NeurIPS 2025), and embodied AI. Possible connections:
--       (1) formalizing 3D spatial geometry (rotations, projections) used
--       in your spatial reasoning work, (2) formalizing audio processing
--       math behind your audio-visual pipeline, (3) formalizing metric
--       spaces or embeddings relevant to multimodal learning.
--
-- 4. Q: I don't want to do anything CV or vision related for this. I'm
--       more interested in the audio side — specifically spatial audio
--       and binaural audio DSP. What could I formalize there?
--    A: Binaural audio DSP has several math-heavy components: (1) discrete
--       convolution — core of all audio filtering, (2) HRTF modeling —
--       filtering for spatial perception, (3) ITD/ILD — geometric models
--       for sound localization, (4) Ambisonics — spherical harmonic
--       encoding of spatial sound fields. All are unexplored in Lean 4.
--
-- 5. Q: Can you break down what each of those four topics involves
--       mathematically? I want to understand what I'd actually be proving.
--    A: (1) Convolution: algebraic properties of Σ_k f[k]·g[n-k] —
--       commutativity, associativity, linearity, delta identity.
--       (2) HRTF: applying convolution to model how head/ear shape filters
--       sound — basically defining HRTF filtering as convolution.
--       (3) ITD: geometric formula ITD(θ) = (r/c)(θ + sin θ) — prove
--       symmetry, monotonicity using trig and calculus.
--       (4) Ambisonics: 3x3 rotation matrices acting on sound field
--       channels — prove orthogonality, determinant, composition.
--
-- 6. Q: Which of these are realistic for 5 weeks and which are too hard?
--       I've also seen you can do DFT and spherical harmonics — what about
--       those?
--    A: Feasible: convolution properties (core work), ITD geometry (clean
--       and small), HRTF as convolution application (builds on conv),
--       first-order Ambisonics rotation (concrete 3x3 matrices). Too hard:
--       full DFT + convolution theorem (need to build DFT from scratch),
--       spherical harmonics (Legendre polynomials + sphere integration),
--       ILD (diffraction series expansions). Stick to the feasible four.
--
-- 7. Q: I think doing all four feasible topics makes sense — convolution,
--       ITD, HRTF, and Ambisonics rotation. Topics 1-3 form a binaural
--       DSP foundation, and topic 4 adds a higher-order spatial audio
--       layer. Does that work as a project?
--    A: Yes, that's a strong structure. Part A (convolution + ITD + HRTF)
--       is the guaranteed core — self-contained and solid on its own.
--       Part B (Ambisonics rotation) is a stretch goal that adds variety
--       by using linear algebra instead of summations. Even if Part B is
--       incomplete, Part A is already a full project.
--
-- 8. Q: What Mathlib infrastructure exists for all this? I don't want to
--       spend 5 weeks just fighting missing library support.
--    A: Convolution: Finset.sum, Finsupp — good. ITD: Real.sin/cos,
--       HasDerivAt, MonotonOn — well-covered. HRTF: just uses convolution
--       you already defined. Ambisonics: Matrix (Fin 3) (Fin 3) ℝ,
--       transpose, fin_cases tactic — workable. Main gap: no built-in
--       convolution or DFT definition, but you define those yourself.
--
-- Phase 2: Technical deep dive into each topic
--
-- 9. Q: For convolution, how do I represent signals? Just ℤ → ℝ?
--    A: Yes, ℤ → ℝ is standard for discrete-time signals. For finite
--       signals, Fin n → ℝ works with Mathlib's Finset.sum. Start with
--       ℤ → ℝ for the theory.
--
-- 10. Q: What about the delta function for the convolution identity?
--     A: Define δ[n] = if n = 0 then 1 else 0. Then prove (f * δ) = f
--        by showing only the k=0 term survives in the sum. Good early
--        lemma to build confidence.
--
-- 11. Q: For ITD, could I formalize the Woodworth model? What properties
--        would I prove?
--     A: Define ITD(θ) = (r/c)(θ + sin θ). Prove: ITD(0) = 0 (no delay
--        from the front), ITD(-θ) = -ITD(θ) (left-right symmetry), and
--        monotonicity on [0, π/2] via derivative 1 + cos θ ≥ 0.
--
-- 12. Q: The monotonicity proof needs calculus. Does Mathlib have what
--        I need — derivatives, cos θ ≥ -1, monotonicity lemmas?
--     A: Yes. HasDerivAt for derivatives, Real.neg_one_le_cos for the
--        bound, and MonotonOn from nonneg derivative. All in Mathlib.
--
-- 13. Q: For the Ambisonics part, what exactly would I define and prove
--        about rotation matrices?
--     A: Define R_z(α) as the 3x3 z-axis rotation matrix using Mathlib's
--        !![...] notation. Prove: (1) orthogonality R^T R = I using
--        sin² + cos² = 1, (2) det R = 1, (3) composition R(α)·R(β) =
--        R(α+β) using sin/cos addition formulas. Use fin_cases to split
--        Fin 3 into cases 0, 1, 2 automatically.
--
-- 14. Q: Is the Ambisonics part going to be painful with Fin 3 indexing
--        and matrix types?
--     A: Less than you'd think. With !![...] for concrete matrices and
--        fin_cases + simp for proofs, Lean handles 3x3 matrices well.
--        The main work is just making sure simp knows sin_sq_add_cos_sq
--        and the addition formulas. Budget 1-2 days for setup.
--
-- Phase 3: Planning and feasibility
--
-- 15. Q: What would milestones look like week by week?
--     A: Week 1: signal types, convolution def, delta function, conv_delta.
--        Week 2: convolution commutativity and associativity. Week 3:
--        linearity, ITD model, ITD symmetry and zero properties. Week 4:
--        ITD monotonicity, rotation matrix def, orthogonality proof.
--        Week 5: rotation composition, cleanup, README, presentation.
--
-- 16. Q: What are the main gotchas I should watch out for?
--     A: (1) Summation reindexing for convolution commutativity — the
--        variable substitution k → n-k is tedious in Lean. (2) ℤ vs ℕ
--        coercions everywhere. (3) Infinite vs finite sum — make sure
--        your convolution def matches the standard one. (4) Matrix
--        dimension unification — Fin 3 sometimes confuses the elaborator.
--
-- 17. Q: What if I get stuck on a Mathlib lemma I can't find?
--     A: Use exact?, apply?, and Moogle (Mathlib search engine). If truly
--        stuck, use sorry and document it. The grading values structure
--        and effort over completeness.
--
-- 18. Q: Should I use tactic proofs or term-level proofs?
--     A: Mix both. Tactics (simp, ring, omega, fin_cases) for algebraic
--        and case-split steps. Term-level (fun, match, ⟨,⟩) for proof
--        structure. Showing range is good for the course.
--
-- 19. Q: Is this novel enough? I don't want it to be textbook exercises.
--     A: Formalizing spatial audio DSP in Lean 4 has never been done.
--        The combination of convolution theory + ITD geometry + Ambisonics
--        rotation as a coherent spatial audio formalization is genuinely
--        new. It also connects to your published research (SAVVY).
--
-- 20. Q: What's the minimum viable outcome if things go wrong?
--     A: Convolution definition + commutativity + delta identity alone
--        is already a solid deliverable. Everything beyond that — ITD,
--        HRTF, Ambisonics — is bonus. Structure Part A as the guaranteed
--        core so you always have something to present.
--
-- Project idea: Formalizing binaural audio DSP foundations in Lean 4.
-- Part A (core): define discrete signals, discrete convolution, and prove
-- algebraic properties (commutativity, associativity, linearity, delta
-- identity). Define HRTF filtering as convolution. Formalize the Woodworth
-- ITD model ITD(θ) = (r/c)(θ + sin θ) and prove symmetry, monotonicity.
-- Part B (stretch): define first-order Ambisonics rotation matrices and
-- prove orthogonality, det = 1, and rotation composition.
-- Uses Mathlib's Finset.sum, Real.sin/cos, HasDerivAt, and Matrix APIs.
