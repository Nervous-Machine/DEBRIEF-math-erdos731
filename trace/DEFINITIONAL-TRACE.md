# Definitional trace of the formal statements for Erdős Problem #731

**For:** a number theorist willing to spend thirty to forty-five minutes, not a day, deciding whether the claimant's
Lean statements for Erdős Problem #731 answer the problem Erdős, Graham, Ruzsa and Straus posed. Two questions on
this record need a person: do the formal statements say what they appear to say (gap EG2), and does the claimant's
formalisation of the word "reasonable", dyadic regularity, answer the problem as posed (gap EG4). This guide is built
so that both can be answered from it, and it puts the second one as a single question in Part E.

**What this is.** The problem as posed, the third-party formal statement and the claimant's headline statements
verbatim, every definition they depend on down to Mathlib with file and line, a plain-language rendering of each
piece, worked examples written for Lean, the places where a formal statement and the problem differ, and a sign-off
checklist. The renderings are the reading of the operating agent (Claude Code, for Nervous Machine) on 17 November
2026. They are an aid, not a check.

**What this is not.** Not an independent human semantic review, and it changes no standing. It is not a build:
nobody outside the claimant has built the Lean development (gap EG1 is open), so every Lean text below is quoted from
source files fetched read-only at the pinned commits, not printed by Lean, and the worked examples in Part D are
written but **not yet run**. It says nothing about the paper's argument (gap EG3).

**Sources, pinned.**
- Problem page: https://www.erdosproblems.com/731 as read on 2026-11-17 (page last edited 19 October 2025), its
  discussion thread and its proof-claims entry.
- Third-party formal statement: `FormalConjectures/ErdosProblems/731.lean` in google-deepmind/formal-conjectures at
  commit `e028240a61822d970c933f4656f51da025cf200b` (blob `1ca01c40`, file sha256 `8721b0dd82f9ab5f…`), and its density
  definitions in `FormalConjecturesForMathlib/Data/Set/Density.lean` (blob `21a7fac9`). That repository pins Lean
  `v4.33.1` and Mathlib `0df444a3`.
- The claim: github.com/ericlisg/erdos731 at commit `cb1b58c88bf639bb87664dd96ffc327c305e160e`:
  `RequestProject/Erdos731/Defs.lean` (blob `1865faab`), `Final.lean` (`58babbd4`), `Downstream.lean` (`ab1a8133`),
  `DyadicExamples.lean` (`ba6058ec`), `paper_source.tex` (`d0626b95`, the paper's source as committed), and the
  README's "Statement audit" section. Every declaration the README quotes was compared with the source file: all ten
  match up to whitespace.
- Mathlib at revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365` and Lean core `v4.28.0`, the versions the claimant's
  `lake-manifest.json` and `lean-toolchain` pin.
- Pre-registration for this trace: `prereg_trace.yaml` (hashed and committed before any definition below was read).

---

## 0. Conventions a reviewer has to know

| convention | where | what it means here |
|---|---|---|
| `Nat.centralBinom n = (2 * n).choose n` | `Mathlib/Data/Nat/Choose/Central.lean` l.36 | $\binom{2n}{n}$; it is always positive (l.42) |
| `sInf` of a set of naturals is its least element, or 0 if the set is empty | `Mathlib/Data/Nat/Lattice.lean` l.29–30 | the claimant's `A` and formal-conjectures' `leastNonDivisor` are "least element of a set". The set is never empty ($\binom{2n}{n}+1$ is in it), so the junk value 0 does not arise. |
| `Real.log 0 = 0`, and `Real.log x = Real.log \|x\|` for $x<0$ | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` l.44, l.102, l.114 | expressions like $\log\log n$ have finite, meaningless values for $n \le 2$. They touch finitely many $n$ and so no density statement. |
| `Real.sqrt x = 0` for $x \le 0$ | `Mathlib/Data/Real/Sqrt.lean` l.109, l.139 | as above, only at small $n$ |
| `x ^ (y : ℝ)` is the real power, defined through ℂ | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` l.35 | $(\log n)^{1/4}$ with $\log n \ge 0$ is the usual fourth root |
| Division by zero is zero | all Lean fields | $x / 0 = 0$. It matters only for formal-conjectures' free `answer` function (D6); the claimant requires $f > 0$. |
| `Filter.limsup u atTop` is `sInf {a \| eventually u ≤ a}` | `Mathlib/Order/LiminfLimsup.lean` l.54, l.64 | the usual limsup for a bounded sequence; the claimant's `upperDensity` applies it to ratios in $[0,1]$, so it is the usual upper density |
| `Set.ncard` of an infinite set is 0 | `Mathlib/Data/Set/Card.lean` l.570, l.598 | every set counted below is intersected with a finite interval first, so this never applies |
| `Filter.Tendsto f atTop (nhds c)` | `Mathlib/Order/Filter/Defs.lean` l.319; `AtTopBot/Defs.lean` l.39 | $f(x) \to c$ as $x \to \infty$ |

---

## Part A. The problem as posed

**A1. The problem page**, verbatim (erdosproblems.com/731, citing [EGRS75], Erdős, Graham, Ruzsa and Straus,
*On the prime factors of $\binom{2n}{n}$*, Math. Comp. 29 (1975), 83–92):

> Find some reasonable function $f(n)$ such that, for almost all integers $n$, the least integer $m$ such that
> $m\nmid \binom{2n}{n}$ satisfies $m\sim f(n)$.

The page adds that EGRS say it is "not hard to show that", for almost all $n$, the minimal such $m$ satisfies
$m=\exp((\log n)^{1/2+o(1)})$.

**A2. The discussion thread.** A comment of 26 April 2026 gives a heuristic (Kummer's theorem plus a Poisson
assumption across primes) with the scale $\sqrt2\,(\log 2)^{1/4}(\log x)^{1/4}\exp\sqrt{(\log 2)\log x}$ and the
suggestion that "there is no function $f(n)$ with $a(n)\sim f(n)$ for almost all $n$, unless the Poisson heuristic is
misleading." The claim makes that heuristic rigorous in the form stated in Part B.

**A3. The claimant's reading of "reasonable"** (paper, `def:dyadic-regular` and §"Why dyadic regularity is the right
formalization", `paper_source.tex` l.499–557): "The word 'reasonable' in the original problem is not formal." The paper
defines a positive $f$ to be *dyadically regular* if $\sup_{X\le m,n<2X}|\log f(m)-\log f(n)|\to 0$, notes that every
$f(n)=\exp(g(\log n))$ with $g'(t)\to 0$ qualifies (powers of $\log n$, iterated logarithms, $\exp(c\sqrt{\log n})$ and
smooth products of these), and asserts: "What dyadic regularity excludes is also exactly what the word 'reasonable' is
meant to exclude. A function that oscillates by a fixed factor inside a dyadic block would have to encode arithmetical
information on the scale of the base-$p$ digit restrictions defining $A(n)$."

**What the trace does not check.** Whether the page's sentence is a faithful rendering of [EGRS75], and whether the
1975 paper says anything more precise about "reasonable". The operating agent did not read the 1975 paper. Checklist
item A0 is for a reviewer who has it.

---

## Part B. The formal statements, verbatim

**B1. formal-conjectures** (`FormalConjectures/ErdosProblems/731.lean` at the pinned commit, namespace `Erdos731`;
the proofs are `sorry` there because the file states problems, it does not solve them):

```lean
noncomputable def leastNonDivisor (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ¬ m ∣ n.centralBinom}                                  -- l.37–38

def erdos_731.answer : ℕ → ℝ := sorry                                         -- l.61

@[category research open, question value, AMS 11]
theorem erdos_731 : ∀ ε > (0 : ℝ),
    {n : ℕ | |(leastNonDivisor n : ℝ) / erdos_731.answer n - 1| < ε}.HasDensity 1 := by
  sorry                                                                         -- l.71–74
```

Its docstring repeats the page's sentence and adds: "Here 'almost all' means natural density $1$, and $m \sim f(n)$
means that for every $\varepsilon>0$ the set of $n$ with $|m/f(n)-1|<\varepsilon$ has density $1$." The word
"reasonable" is in the docstring only; the formal text places no condition on `answer`. The file also states the EGRS
remark as a separate variant, `erdos_731.variants.egrs75` (l.85–88, tagged `research solved`, proof `sorry`): for every
$\varepsilon>0$, $\exp((\log n)^{1/2-\varepsilon}) < A(n) < \exp((\log n)^{1/2+\varepsilon})$ on a set of density 1.

`Set.HasDensity S α` is `Tendsto (fun b => S.partialDensity Set.univ b) atTop (𝓝 α)` (`Density.lean` l.91–93), with
`partialDensity` the proportion of $\{0,\dots,b-1\}$ lying in $S$ (l.42–44).

**B2. The claimant's headline statements** (`RequestProject/Erdos731/Final.lean` at `cb1b58c8`):

```lean
theorem no_dyadically_regular_equivalent_unconditional :
    ¬ ∃ f : ℕ → ℝ, dyadicRegular f ∧ tendstoOneInDensity (fun n => (A n : ℝ) / f n)   -- l.74–75

theorem global_density_tight_unconditional :
    Odens (fun n => Real.log (A n)
        - Real.sqrt (cval * Real.log n) - (1 / 4) * Real.log (Real.log n))            -- l.79–81
```

The README's "Paper-to-Lean map" pairs these with the paper's `thm:no-equivalent` and `cor:global`. The claimant reports
that both depend only on `propext`, `Classical.choice`, `Quot.sound`; that is gap EG1's to confirm, not this trace's.

**B3. A supporting statement that matters for the reading** (`Downstream.lean` l.120–124 and l.141–145; the paper's
`cor:inherited-oscillation`). It is proved from `Nonconcentration`, which `nonconcentration_of_main` (l.67) derives from
the mesoscopic tail bounds, which `mesoscopicTailBounds_per_z` (`Final.lean` l.68) asserts outright:

```lean
def InheritedOscillation (f : ℕ → ℝ) : Prop :=
  ∃ α β η : ℝ, 0 < α ∧ α < β ∧ 0 < η ∧
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → 1 ≤ X →
      η ≤ PP X {n | f n ≤ α * calF X} ∧
      η ≤ PP X {n | β * calF X ≤ f n}

theorem inherited_oscillation
    (hmain : Nonconcentration)
    (f : ℕ → ℝ) (hf : ∀ n, 0 < f n)
    (hconv : tendstoOneInDensity (fun n => (A n : ℝ) / f n)) :
    InheritedOscillation f
```

**B4. The bridge to formal-conjectures.** None exists. B1 asks for a function; B2 proves that no function in a class
works. The two developments also sit on different toolchains (Lean `v4.28.0` against `v4.33.1`), so B1 cannot be
quoted into the claimant's development and closed by `exact` as was done for problem 306. Part D, example 4 writes B1's
shape in the claimant's vocabulary as `FCShape f`, and the negative theorem as `∀ f, dyadicRegular f → ¬ FCShape f`;
that restatement is not proved anywhere (D6).

---

## Part C. Every piece, traced

Claimant's definitions are in `RequestProject/Erdos731/Defs.lean` unless another file is named.

| piece | Lean meaning, with source | agent's reading |
|---|---|---|
| `A n` | `sInf (nonDivisors n)` (l.33), `nonDivisors n = {m \| 1 ≤ m ∧ ¬ (m ∣ B n)}` (l.29), `B n = Nat.centralBinom n` (l.26) | $A(n)$ = the least $m \ge 1$ with $m \nmid \binom{2n}{n}$. Same function as B1's `leastNonDivisor` (`0 < m` there, `1 ≤ m` here). |
| `dyadicRegular f` | `(∀ n, 0 < f n) ∧ ∀ ε > 0, ∃ X₀, ∀ X ≥ X₀, ∀ m n, X ≤ m < 2X → X ≤ n < 2X → \|log f m − log f n\| ≤ ε` (l.61–65) | "$f>0$, and $\sup_{X\le m,n<2X}\|\log f(m)-\log f(n)\| \to 0$ as $X\to\infty$": the logarithm of $f$ is asymptotically constant on every window $[X,2X)$, for every integer $X$, not only powers of 2 (D4). |
| `tendstoOneInDensity g` | `∀ ε > 0, #{n < N : ε < \|g n − 1\|} / N → 0` (l.79–83) | "$g(n) \to 1$ in natural density". With $g = A/f$: "$A(n) \sim f(n)$ for almost all $n$" in the standard density sense, the same as B1's docstring (D5). |
| `¬ ∃ f, dyadicRegular f ∧ tendstoOneInDensity (A / f)` | B2, `Final.lean` l.74–75 | "No dyadically regular $f$ has $A(n)\sim f(n)$ for almost all $n$." |
| `upperDensity E` | `limsup_N #(E ∩ [1, N]) / N` (l.69–70) | the usual upper natural density |
| `Odens R` | `upperDensity {n \| C < \|R n\|} → 0` as $C \to \infty$ (l.74–75) | "$R(n) = O(1)$ in density": for every $\delta>0$ there is $C$ with $\|R(n)\| \le C$ outside a set of upper density $\le\delta$ |
| `cval` | `Real.log 2` (l.36) | $c = \log 2$ |
| `R n = log (A n) − √(cval · log n) − ¼ log (log n)` | B2, `Final.lean` l.79–81 | $\log A(n) - \sqrt{(\log 2)\log n} - \tfrac14\log\log n$ |
| `Odens R` for that R | B2 | "$\log A(n) = \sqrt{(\log2)\log n} + \tfrac14\log\log n + O(1)$ for almost all $n$, with the $O(1)$ uniform in density": $A(n)$ is within a bounded factor of $F(n)$ outside sets of arbitrarily small upper density. It does not give an $f$ with $A \sim f$. |
| `F n` | `1` for $n \le 1$, else `√2 · (log 2)^(1/4) · (log n)^(1/4) · exp √(log 2 · log n)` (l.53–56) | the paper's scale $F(n)$. It does not occur in B2's statement; $\log F(n)$ differs from B2's centring by the constant $\log\sqrt2 + \tfrac14\log\log 2$, which `Odens` ignores (`Global.lean` l.77). |
| `calF X`, `u0`, `sval`, `Ldef` | `calF X = exp (u0 X)`, `u0 X = sval X + ½ log (2 · sval X)`, `sval X = √(cval · Ldef X)`, `Ldef X = log (2X)` (l.39–48) | $\mathcal F_X = \sqrt2\,(\log2)^{1/4}L^{1/4}\exp\sqrt{(\log 2)L}$ with $L=\log 2X$: the scale on the block $[X,2X)$ |
| `PP X E` | `#(E ∩ [X, 2X)) / X` (l.86–87) | the proportion of the block $[X,2X)$ lying in $E$ |
| `InheritedOscillation f` | B3 | "on every large block, $f \le \alpha\mathcal F_X$ on at least a proportion $\eta$ and $f \ge \beta\mathcal F_X$ on at least a proportion $\eta$", with fixed $0<\alpha<\beta$ |
| `inherited_oscillation` | B3, with hypothesis supplied by `nonconcentration_of_main` | "any positive $f$ with $A(n)\sim f(n)$ for almost all $n$ swings by at least the fixed factor $\beta/\alpha$ inside every large block, each extreme on a positive proportion of it." The negative headline theorem is this plus "a dyadically regular $f$ cannot swing" (`Downstream.lean` l.188–210). |
| `dyadicRegular_F`, `not_dyadicRegular_A` | `DyadicExamples.lean` l.106, l.352 | the class is not empty ($F$ is in it) and $A$ itself is not in it. The second is derived from the headline theorem, so it guards only against an empty class, not against a too-narrow one. |
| `dyadicRegular_exp_log_of_hasDerivAt_tendsto_zero` | `DyadicExamples.lean` l.30–33 | every $f(n) = \exp(g(\log n))$ with $g$ differentiable and $g' \to 0$ is dyadically regular (the paper's `rem:dyadic-examples`) |

---

## Part D. Worked examples, written but not yet run

The commands are in `cycles/trace-1/Trace.lean`. **None has been run by Lean.** They need the claimant's built
development, which Nervous Machine has not built (EG1). Values given here are the operating agent's, computed in
Python or by hand, and are marked so; when the file is run inside the built development, its output goes in
`cycles/trace-1/trace.txt` as a separate cycle and replaces these.

1. Small values (`#eval`). Agent's values: for $n = 0, \dots, 12$, $\binom{2n}{n} = 1, 2, 6, 20, 70, 252, 924, 3432,
   12870, 48620, 184756, 705432, 2704156$ and $A(n) = 2, 3, 4, 3, 3, 5, 5, 5, 4, 3, 3, 5, 3$. $A$ wanders between small
   prime powers from one $n$ to the next; that is the behaviour the negative theorem is about.
2. `0 ∉ nonDivisors n`, `B 1 = 2`, `A 1 = 3`, and `0 < A n` for every $n$: the claimant's `A` excludes $m = 0$ and
   agrees with formal-conjectures' `leastNonDivisor`, which the formal-conjectures file itself checks at $n=1$
   (`leastNonDivisor_one`, l.50).
3. Edge conventions: `Real.log 0 = 0`, `Real.log 1 = 0`, `Real.log (-2) = Real.log 2`, `Real.sqrt (-1) = 0`,
   `(1 : ℝ) / 0 = 0`, `F 0 = 1`, `F 1 = 1`.
4. `FCShape (fun n => A n)`: B1 with `answer := A` holds, because the ratio is identically 1. So B1 without the word
   "reasonable" has no content (D6). `NoDyadicallyRegularFCShape`, the negative theorem in B1's shape, is stated and
   not proved.
5. Floating-point illustration (not a proof) of what the class excludes. On sample points of the block
   $[2^{20}, 2^{21})$, $\log F$ spreads by about 0.089 (and the spread tends to 0 further out), while
   $\log\big(F(n)\,(2+\sin(2\pi\log_2 n))\big)$ spreads by about 1.05, tending to $\log 3 \approx 1.10$ and never to 0
   (agent's Python). The second function is smooth in $\log n$ and is not dyadically regular, so B2 says nothing about it.
6. `#print` of every claimant definition in Part C and of `Nat.centralBinom`, `Real.log`, `Real.sqrt`,
   `Filter.limsup`; `#check` of B2, B3, `dyadicRegular_F`, `not_dyadicRegular_A`, `A_isPrimePow`; `#print axioms` of
   the two headline theorems and `inherited_oscillation`.

---

## Part E. Discrepancies and observations

| id | observation | kind | effect, in the agent's reading |
|---|---|---|---|
| D1 | "Reasonable" is formalised as dyadic regularity: $\log f$ asymptotically constant on each block $[X,2X)$. The class leaves out smooth functions whose logarithm moves by a bounded nonzero amount inside each block, for example $F(n)\,(2+\sin(2\pi\log_2 n))$ (Part D, example 5). B3 shows that any $f$ that works must swing by a fixed factor inside every block on positive proportions; it does not show that a smooth swinging $f$ fails. The paper argues such an $f$ "would have to encode arithmetical information"; for a function of $\log n$ alone that is an argument, not a theorem in the development. A plausible route to exclude it (tail bounds on short windows $[X,(1+\delta)X)$, so that the spread of $A$ does not depend on position in the block) is not stated in the development. | the claimant's disclosed formalisation choice | **uncertain; could change the meaning.** If a reviewer counts such functions as possibly reasonable, the Lean statements leave the problem open for them. If not, B2 answers the problem. Already gap EG4; recorded here and put as checklist item A4, not opened as an anomaly (the choice is disclosed; `prereg_trace.yaml` R3). |
| D2 | The problem asks to find an $f$; the claim answers that no reasonable $f$ exists, and offers instead $F$ up to a bounded factor in density (B2, second statement). | shape of the answer | part of the same judgment as D1: whether "none exists; here is the scale up to $O(1)$ in $\log$" resolves "find $f$". The positive half is strictly weaker than $A\sim F$ and is not claimed to be more. |
| D3 | The phrase "$F$ is the best possible deterministic scale" (paper and README) has no single Lean statement; it is the combination of B2's two theorems. | wording | none; a reader should not look for a separate "best possible" theorem. |
| D4 | `dyadicRegular` constrains every window $[X,2X)$ with $X$ an integer, not only $[2^k, 2^{k+1})$, and requires $f(n)>0$ for every $n$, including $n=0$. | definition detail | none. The every-window version is slightly smaller than the powers-of-two version (which would allow a fixed jump at each $2^k$) and matches the paper's definition; positivity is needed for $\log f$ and costs nothing for a candidate asymptotic. |
| D5 | Density conventions: the claimant counts $\{n<N : \varepsilon < \|g(n)-1\|\}$ and asks the proportion $\to 0$; formal-conjectures counts $\{n<N : \|g(n)-1\| < \varepsilon\}$ and asks $\to 1$. `upperDensity` counts $[1,N]$; `Odens` and `PP` use their own windows. | convention | none: strict against non-strict at $\varepsilon$ is immaterial because $\varepsilon$ is arbitrary, and the windows differ by at most one point. `A` is the same function in both (Part D, example 2). |
| D6 | The formal-conjectures statement B1 places no condition on `answer`, so `answer := leastNonDivisor` satisfies it (Part D, example 4); its form (`question value`) also presupposes a positive answer, while the claim's headline is negative. The two developments are on different toolchains. | third-party formalisation | none on the claim's meaning, but B1 cannot serve as the machine reference it was for problem 306. Reading the claim against the problem goes through the claimant's own statements (B2, B3), and the meaning question sits entirely in D1. |
| D7 | B2's second statement centres at $\sqrt{(\log 2)\log n}+\tfrac14\log\log n$, not at $\log F(n)$, and uses `Real.log` at small $n$ where $\log\log n$ is not the usual value. | convention | none: the centrings differ by a constant, which `Odens` absorbs (`Odens_add_const`, `Global.lean` l.77), and small $n$ are finitely many. |
| D8 | The paper's `thm:main` holds uniformly for $1\le z\le Z(X)=o(L^{1/4})$; the Lean `MesoscopicTailBounds` is the fixed-$z$ form. | scope, disclosed by the claimant | none for B2, which uses only the fixed-$z$ form (`Final.lean` l.74–82). It matters only to a reader who takes the repository as covering the paper's main theorem in full. |
| D9 | formal-conjectures' solved variant `egrs75` (EGRS's own remark) has no counterpart in the claimant's development. In the agent's reading B2's second statement implies it. | coverage | none on meaning; an optional bridge a Lean user could write. |

One discrepancy, D1 (with D2 as its other face), could change what the claim answers, in the agent's reading. It is
the choice the claimant discloses, so no anomaly is opened; it is put to a reviewer as A4 below. No undisclosed
difference was seen: `A` is the problem's $A(n)$, the density notion is the standard one, and the README's quoted
statements match the source files.

---

## Part F. Sign-off checklist

For a reviewer who is prepared to put their name to a reading. Each line is a yes/no. Send it with the **Semantic read**
issue form on this repository (it becomes a `read` cycle under your name), or anywhere public; the ledger records it by
date. A1 to A3 bear on gap EG2, A4 and A5 on gap EG4. Two independent signatures with no refusal close a gap; one
refusal reopens it.

- [ ] A0 (optional, needs the 1975 paper): the page's sentence is the problem of Erdős, Graham, Ruzsa and Straus, and the paper gives "reasonable" no more precise meaning.
- [ ] A1: `A`, with `tendstoOneInDensity (fun n => A n / f n)`, is "the least $m \nmid \binom{2n}{n}$ satisfies $m\sim f(n)$ for almost all $n$" (Part C; D4, D5).
- [ ] A2: `no_dyadically_regular_equivalent_unconditional` reads "no positive $f$ whose logarithm is asymptotically constant on every $[X,2X)$ has $A(n)\sim f(n)$ for almost all $n$" (B2; D4).
- [ ] A3: `global_density_tight_unconditional` reads "$\log A(n) = \sqrt{(\log 2)\log n} + \tfrac14\log\log n + O(1)$ outside sets of arbitrarily small upper density", and nothing stronger (B2; D7).
- [ ] A4: No function you would call "reasonable" in the problem's sense lies outside the class while swinging by a bounded factor inside each block, as $F(n)(2+\sin(2\pi\log_2 n))$ does; or, if one does, B3 or a routine short-window version of the paper's tail bounds rules it out (D1).
- [ ] A5: "No reasonable $f$ exists; $F$ is the right scale up to a bounded factor in density" is an answer to the problem as posed (D2).

The question that matters most, put plainly: the claim's Lean theorems rule out every $f$ whose logarithm is nearly
constant on each block $[X,2X)$, and show that any $f$ that worked would have to swing by a fixed factor inside every
block. Would you count such a swinging function, for example $F(n)(2+\sin(2\pi\log_2 n))$, as "reasonable"? If not,
A4 is signed and the negative answer stands as an answer to the problem; if so, does the paper's argument extend
routinely to short windows $[X,(1+\delta)X)$ to exclude it too?
