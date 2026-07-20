# lol_jacobian_conjecture

A machine-checked case study of a map that *looks like* it refutes the Jacobian
Conjecture over ℂ — and a demonstration of why "the arithmetic is flawless" is
not the same thing as "the conjecture is false."

The Lean is real. The green checks are real. The conclusion is (almost
certainly) a trap. That gap is the entire point of this repo.

## TL;DR

Consider

```
F(x, y, z) = ( (1+xy)³·z + y²(1+xy)(4+3xy),
               y + 3x(1+xy)²·z + 3xy²(4+3xy),
               2x − 3x²y − x³z )
```

Machine-verified, in exact arithmetic, three independent ways (plus Wolfram Alpha
and SymPy externally):

| Fact | Status |
|------|--------|
| `det J(F) ≡ −2` — a nonzero **constant** polynomial | ✅ verified symbolically **and** by exact-rational analytic partials at 5 generic points |
| `F(0,0,−¼) = F(1,−³⁄₂,¹³⁄₂) = F(−1,³⁄₂,¹³⁄₂) = (−¼,0,0)` — **not injective** | ✅ verified in exact ℚ |
| `F` has **no polynomial inverse** (formal series never terminates) | ✅ formal power-series inverse computed to degree 5, residual 0, term-count growing |

Taken at face value, `constant nonzero Jacobian + non-injective` is **logically
incompatible with the Jacobian Conjecture over ℂ**. `Counterexample.lean` even
returns `contradicts_JC_over_C = true`.

**So did we disprove an 85-year-old conjecture with a screenshot? No. Read on.**

## The Jacobian Conjecture

> (Keller, 1939.) If `F : ℂⁿ → ℂⁿ` is a polynomial map whose Jacobian
> determinant is a nonzero constant, then `F` is bijective (with polynomial
> inverse).

Still open for all `n ≥ 2`. Bass–Connell–Wright (1982) reduced the whole problem
to **degree-3 maps** — which is exactly the degree of `F` above. That reduction
is why this repo's "counterexample" should set off every alarm you have: cubic
maps in low dimension are the single most-scrutinized objects in the field. A
degree-3, integer-coefficient, rational-preimage counterexample is the *first*
thing anyone would have tried. If it worked, the conjecture would have died in
1939.

## Why this is (almost certainly) not a refutation

The arithmetic is airtight and independently reproduced. That is **exactly why you
should be more suspicious, not less.** Every historical near-miss on this
conjecture had correct arithmetic; the flaw was always in the *framing*, never the
algebra, and the cleaner the algebra the better-hidden the catch.

The base-rate argument is decisive:

- Open since **1939**; reduced to the cubic case since **1982**.
- A clean cubic counterexample with integer coefficients would be in every
  textbook, not arriving via an AI-generated screenshot.
- The map's structure — everything built from `u = 1+xy`, graded coefficients,
  tidy rational fibers — is the signature of an object **reverse-engineered to
  pass exactly the checks a skeptic runs.**

The most likely explanation: this is an **AI fabrication** whose individual
arithmetic facts are mutually self-consistent, wrapped in a hallucinated
"counterexample to the Jacobian Conjecture" framing. Verifying `det J = −2` and
"two points share an image" does **not** verify that no definitional subtlety
separates this object from the conjecture's actual hypothesis — and that gap is
where the catch lives.

**Machine-checked arithmetic certifies the numbers. It does not certify the
claim.** This repo is a monument to that distinction.

## What's in here

| File | What it checks |
|------|----------------|
| `src/Counterexample.lean` | Capstone. `det J(F) ≡ −2`, three exact preimages of `(−¼,0,0)`, and the boolean `contradicts_JC_over_C`. |
| `src/AnalyticJacobian.lean` | Independent confirmation: exact-rational **hand-differentiated** partials give `det = −2` at 5 generic points (shares no code with the symbolic engine). |
| `src/FormalInverse.lean` | The formal power-series inverse at the origin. Residual `G(F(w))−w = 0` to degree 4; term count grows without terminating ⇒ no polynomial inverse. |
| `src/FiberReduction.lean` | Proves the inversion-reduction identities `idA ≡ idB ≡ 0`, and studies the generic fiber via a resultant. |
| `src/EngineControls.lean` | Sanity controls for the home-grown symbolic engine (identity→1, `(x²,y,z)`→`2x`, swap→−1, `(x+y²,y+z²,z+x²)`→`1+8xyz`, a multiplication check). Confirms the engine itself is trustworthy. |

Everything is **pure Lean 4 core** — a small sparse-multivariate-polynomial
engine over ℤ and an exact ℚ type. No Mathlib dependency, no floating point in
the load-bearing checks.

## Running it

Requires [Lean 4](https://leanprover.github.io/) `v4.32.0` (pinned in
`lean-toolchain`; install via [`elan`](https://github.com/leanprover/elan)).

```sh
lean src/Counterexample.lean     # prints -2, three (-1/4,0,0)'s, and three `true`s
lean src/AnalyticJacobian.lean   # prints -2 five times
lean src/FormalInverse.lean      # inverse-series growth + residual 0
lean src/EngineControls.lean     # engine sanity controls
```

Each file drives its checks with `#eval`; the printed output *is* the
verification.

## The honest verdict

Beautiful, self-consistent, independently reproduced arithmetic — and a
conclusion that is almost certainly a framing error, most likely AI-generated.
The responsible next step is **not** a preprint. It is:

1. A literature search for this exact map (it is far too clean to be novel).
2. Sending these files to a specialist in affine algebraic geometry to locate the
   catch in minutes.
3. Tracing the source. If it has no citable, refereed provenance, that is the
   answer.

If eleven people and four computer-algebra systems can't find the flaw, that
tells you who to ask — not that the flaw isn't there.

## License

MIT. It's a joke repo about a serious conjecture. Do what you like.
