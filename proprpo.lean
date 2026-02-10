import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
--import Mathlib

open BigOperators

#check Finset.induction

#eval ∑ i in Finset.range 5, i   -- 0 + 1 + 2 + 3 + 4 = 10
#eval ∑ i in Finset.Icc 1 (3), i

#check Nat.strong_induction_on


example (a : ℝ) (b : ℝ) (c : ℝ) (h1 : a = b) (h2 : c ≠ 0) : c * a = c * b := by
  exact congrArg (HMul.hMul c) h1

example (a b c d : ℝ) (h1 : a = b) (h2 : c = d) :  a + c = b + d := by
  exact Mathlib.Tactic.LinearCombination.add_pf h1 h2

theorem IneedHelp (a b : ℝ) : a + -1*b = a - b := by
  ring

example (b : ℝ) (h1 : b ≠ 0): b / b = 1 := by
  apply (div_eq_one_iff_eq h1).mpr rfl

example {P Q : Prop} (hp : P) (h : P → Q) : Q := by
  apply h at hp
  exact hp

example {P Q : Prop} (hp : P) (h : P → Q) : Q := by
  apply h
  exact hp
