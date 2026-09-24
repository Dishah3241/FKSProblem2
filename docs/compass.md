# Compass list

These are the declarations whose meaning decides whether the frozen statement says what FKS Problem 2 asks: for
every `d`, every graph on `2d + 1` vertices, or its complement, has a unit-distance representation in `ℝᵈ`.
Equivalently, `f_D(2d + 1) = d` (Alon–Kupavskii 2014; FKS 2020, §5, Problem 2).

This list is the owner's whole review surface, and **its sign-off is the statement freeze** (ROADMAP P9, phase
0). Everything else, including every later proof and the GraphDimension library, is checked by the kernel and the
gates.

**The frozen text** is statement A: `FKSProblem2/Standalone/Mathlib/StatementA.lean`, namespace
`FKSProblem2.StatementA`, at FKSProblem2 `fc71d65`.

**Owner sign-off: confirmed on 2026-09-24 for rows 1–10.** In the open-question manager's session, the owner answered "Sign rows 1–10" to the request to sign this list, as committed at `3e99d59`. The sign-off freezes the statement: statement A at `fc71d65`, blob `026fc7503ebd79967b58c93817d46451156f318a`. Any change to a row cancels it.

The sign-off covers the declarations' names, types and bodies. Two later additions are metadata and change no row's meaning. First, the formal-proof block that `proof-links` needs. Second, the template's open-claim mark on row 3, which is "open problem" in its docstring plus an `open:` line in the proof block. The manager tells the owner when either lands.

## How the statement was made

- **The owner's choices, 2026-09-24:**
  - freeze the whole question as a `Prop`, so that the work can end in a proof or a disproof;
  - take `d = 3`, that is `f_D(7) = 3`, as the first target;
  - scope as in `~/Code/Math/docs/research/2026-09-24-open-question-selection.md` §4.
- **Authored, not inherited.** No `formal-conjectures` statement exists. Stage 1 wrote it twice, blind:
  - statement A by pi (glm-5.3-flash), run `20260924-121415-fb962a89`;
  - statement B by codex (gpt-6-astra), run `20260924-121415-ce68618f`, with its placement written inline and
    the existential outside the disjunction.
- **Equivalence, proved in Lean with no `sorry`.** codex (gpt-6-sol), run `20260924-124350-f8a4755f`, proved in
  `FKSProblem2/Stage1/Equivalence.lean`:
  - `questionAt d ↔ problem2At d` for every `d`;
  - `question ↔ problem2`. A quantifies over every `d : ℕ` and B over `d = n + 1`; the difference is absorbed by
    `questionAt_zero`, a proof that `d = 0` holds;
  - `questionAt3 ↔ problem2Three`.
- **The model names** come from the run logs (`harness/run-model`).

## The rows

| # | Declaration | Must mean | Check |
|---|---|---|---|
| 1 | `HasUnitDistanceRepresentation d G` | there is an **injective** map from the vertices of `G` into `ℝᵈ` with every **edge** at distance exactly 1 | Non-edges are unconstrained and may also be at distance 1 (Erdős–Harary–Tutte, not "faithful"). Note the argument order `d G`. |
| 2 | `questionAt d` | for every simple graph `G` on the vertex set `Fin (2d + 1)`: `G` has a representation in `ℝᵈ`, **or** its complement `Gᶜ` has one | `Fin (2d + 1)` covers every graph on `2d + 1` vertices up to relabelling. The placement may depend on `G`, and the disjunct may too. |
| 3 | `question` | `questionAt d` for **every** natural number `d` | The source asks for positive `d`. `d = 0` (one vertex in `ℝ⁰`) holds, and `Stage1.questionAt_zero` proves it, so nothing is added. This is the frozen open question; it is not claimed proved. |
| 4 | `questionAt3` | every simple graph on 7 vertices, or its complement, has a representation in `ℝ³` | The first target, phase 1. With FKS Theorem 4's lower bound it is exactly `f_D(7) = 3`. It is written over `Fin 7`, and the kernel checks it agrees with `questionAt 3`. |
| 5 | `questionAt3.witness` | some graph on 7 vertices has **no** representation in `ℝ³`, for example `K₇` | Guards against a trivially true row 4: the complement alternative does real work. |
| 6 | `question.witness` | `questionAt 0` and `questionAt 1` hold | The question's range contains real instances. At `d = 1` the triangle fails in `ℝ¹`, but its complement is edgeless. |
| 7 | `HasUnitDistanceRepresentation.separating` | (a) two vertices with no edges have no representation in `ℝ⁰`, although a non-injective map exists; (b) the star `K₁,₃` has a representation in `ℝ²` in which a **non-edge** is at distance 1 | (a) separates row 1 from the reading without injectivity; (b) separates it from the faithful reading. |
| 8 | `questionAt.separating` | `questionAt 1` holds, but not every graph on 3 vertices itself has a representation in `ℝ¹` | Separates row 2 from the misreading that drops the complement. |
| 9 | Mathlib `Gᶜ` | the complement on the **same** vertex set: distinct `u, v` are adjacent exactly when they are not adjacent in `G` | An isolated vertex of `G` is adjacent to every other vertex of `Gᶜ`. |
| 10 | Mathlib `dist` on `EuclideanSpace ℝ (Fin d)` | the Euclidean (L²) distance | `EuclideanSpace` is `PiLp 2`; the plain `Fin d → ℝ` would carry the sup metric. |

## Not part of the freeze

- **Which declaration Palomar sees.** At phase 1's release, `Challenge.lean` states `questionAt3`, copied from row 4
  with `Iff.rfl` back to A.
- **The companions' proofs** (rows 5–8). Their statements are frozen above. Their proofs are a small leaf before the
  gates.
- **How the template carries row 3.** The template's `proof-links` audit expects every closed claim to be proved,
  and row 3 is open. The Math manager (math-78) is asked for an "open claim" convention that keeps its fidelity
  companions. Row 3's meaning does not change.
