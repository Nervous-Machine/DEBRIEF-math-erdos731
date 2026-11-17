/-
Cycle 1 of DEBRIEF-math-erdos731: worked examples for the definitional trace (trace/DEFINITIONAL-TRACE.md).

STATUS: WRITTEN, NOT YET RUN BY LEAN. Nervous Machine has not built the claimant's development (gap EG1 is open),
so nothing below has been elaborated or checked by the kernel. Some proofs may need adjusting when it is run.
The trace claims no result from this file.

To run (inside a built checkout of github.com/ericlisg/erdos731 at cb1b58c88bf639bb87664dd96ffc327c305e160e,
Lean v4.28.0, Mathlib 8f9d9cff6bd728b17a24e163c9402775d9e6a365):

    lake env lean /path/to/Trace.lean > trace.txt 2>&1

and commit trace.txt beside this file as a separate cycle. Statements and definitions are referred to by name only;
no claimant code is copied here.
-/
import RequestProject.Erdos731.Final
import RequestProject.Erdos731.DyadicExamples

open Erdos731

/-! ## 1. The statements and definitions, as the development prints them (Parts B and C of the trace) -/

#check @no_dyadically_regular_equivalent_unconditional
#check @global_density_tight_unconditional
#check @inherited_oscillation
#check @nonconcentration_of_main
#check @dyadicRegular_F
#check @not_dyadicRegular_A
#check @A_isPrimePow

#print B
#print nonDivisors
#print A
#print cval
#print F
#print calF
#print u0
#print sval
#print Ldef
#print dyadicRegular
#print upperDensity
#print Odens
#print tendstoOneInDensity
#print PP
#print eventAle
#print eventAgt
#print MesoscopicTailBounds
#print Nonconcentration
#print InheritedOscillation

#print Nat.centralBinom
#print Real.log
#print Real.sqrt
#print Filter.limsup

#print axioms no_dyadically_regular_equivalent_unconditional
#print axioms global_density_tight_unconditional
#print axioms inherited_oscillation

/-! ## 2. Small values of A(n) (Part D, example 1)

`A` is defined with `sInf`, so it cannot be evaluated directly. `lndC` is a computable search written here for the
examples; example 2 ties it to `A` at one value. Expected output (computed by the operating agent in Python, not by
Lean): for n = 0..12, centralBinom = 1, 2, 6, 20, 70, 252, 924, 3432, 12870, 48620, 184756, 705432, 2704156 and
lndC = 2, 3, 4, 3, 3, 5, 5, 5, 4, 3, 3, 5, 3. -/

def lndC (n : ℕ) : ℕ :=
  ((List.range (Nat.centralBinom n + 2)).find? (fun m => 0 < m && Nat.centralBinom n % m != 0)).getD 0

#eval (List.range 13).map Nat.centralBinom
#eval (List.range 13).map lndC
#eval (List.range 41).map lndC

/-! ## 3. A excludes m = 0 (Part D, example 2; discrepancy D5) -/

-- 0 is not in the set A minimises over, so A n ≥ 1 and A agrees with formal-conjectures' leastNonDivisor.
example (n : ℕ) : 0 ∉ nonDivisors n := by
  simp [nonDivisors]

example : B 1 = 2 := by decide

example : A 1 = 3 := by
  have hc : B 1 = 2 := by decide
  have hne : (nonDivisors 1).Nonempty := ⟨3, by simp [nonDivisors, hc]; decide⟩
  rw [A, Nat.sInf_def hne, Nat.find_eq_iff]
  refine ⟨by simp [nonDivisors, hc]; decide, fun m hm => ?_⟩
  interval_cases m <;> simp [nonDivisors, hc]

example (n : ℕ) : 0 < A n := by
  obtain ⟨p, k, hp, hk, h⟩ := A_isPrimePow n
  exact h ▸ pow_pos hp.pos k

/-! ## 4. Conventions at the edges (Part D, example 3; discrepancies D4, D7) -/

example : Real.log 0 = 0 := Real.log_zero
example : Real.log 1 = 0 := Real.log_one
example : Real.log (-2) = Real.log 2 := Real.log_neg_eq_log 2
example : Real.sqrt (-1) = 0 := Real.sqrt_eq_zero_of_nonpos (by norm_num)
example : (1 : ℝ) / 0 = 0 := div_zero 1
example : F 0 = 1 := by simp [F]
example : F 1 = 1 := by simp [F]

/-! ## 5. The formal-conjectures shape is trivially met by A itself (Part D, example 4; discrepancy D1)

`FCShape f` is the formal-conjectures statement `erdos_731` with `answer := f`, written with the claimant's `A` and
with formal-conjectures' `Set.HasDensity` unfolded by hand to its definition (`partialDensity` over `Iio N`). It is a
restatement for reading, not the formal-conjectures declaration itself, which lives on a different Lean toolchain. -/

def FCShape (f : ℕ → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), Filter.Tendsto
    (fun N : ℕ => ((({n : ℕ | |(A n : ℝ) / f n - 1| < ε} ∩ Set.Iio N).ncard : ℝ) / ((Set.Iio N).ncard : ℝ)))
    Filter.atTop (nhds 1)

-- With f := A the ratio is identically 1, so the shape holds and carries no content without the word 'reasonable'.
example : FCShape (fun n => (A n : ℝ)) := by
  intro ε hε
  have hA : ∀ n, (0 : ℝ) < A n := fun n => by
    obtain ⟨p, k, hp, hk, h⟩ := A_isPrimePow n
    exact_mod_cast h ▸ pow_pos hp.pos k
  have hset : {n : ℕ | |(A n : ℝ) / (A n : ℝ) - 1| < ε} = Set.univ := by
    ext n; simp [div_self (hA n).ne', hε]
  rw [hset]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have h0 : ((Set.Iio N).ncard : ℝ) ≠ 0 := by
    rw [Set.ncard_eq_toFinset_card']; simp; omega
  rw [Set.univ_inter, div_self h0]

-- The negative headline theorem, rewritten in this shape (stated, not proved here; the bridge is D6 of the trace):
def NoDyadicallyRegularFCShape : Prop := ∀ f : ℕ → ℝ, dyadicRegular f → ¬ FCShape f
#check NoDyadicallyRegularFCShape

/-! ## 6. What dyadic regularity excludes (Part D, example 5; discrepancy D2)

Floating-point illustration only (not a proof): the spread of log f across sample points of the block [2^20, 2^21)
for f = F and for f = F * (2 + sin(2π log₂ n)). The agent's Python gives about 0.089 for F (and this tends to 0 as the
block moves out) and about 1.05 for the modulated function (tending to log 3 ≈ 1.0986, never to 0). The second
function is smooth and is not dyadically regular, so the negative theorem says nothing about it. -/

def logFf (n : Float) : Float :=
  0.5 * Float.log 2 + 0.25 * Float.log (Float.log 2) + 0.25 * Float.log (Float.log n)
    + Float.sqrt (Float.log 2 * Float.log n)

def logModf (n : Float) : Float :=
  logFf n + Float.log (2 + Float.sin (2 * 3.141592653589793 * Float.log n / Float.log 2))

def blockSpread (g : Float → Float) (X : Nat) : Float :=
  let pts := (List.range 64).map (fun i => (X + i * (X / 64) : Nat).toFloat) ++ [((2 * X - 1 : Nat).toFloat)]
  let vals := pts.map g
  vals.foldl max (vals.headD 0) - vals.foldl min (vals.headD 0)

#eval (blockSpread logFf (2 ^ 20), blockSpread logModf (2 ^ 20), Float.log 3)
#eval (blockSpread logFf (2 ^ 60), blockSpread logModf (2 ^ 60))
