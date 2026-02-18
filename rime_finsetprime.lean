import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorial.Basic
import MIL.Common
--import Mathlib

open BigOperators
#check Nat.Prime


theorem there_inf_prime : ∀ N : ℕ, ∃ p ≥ N, Nat.Prime p := by
    by_contra hneg
    push_neg at hneg
    rcases hneg with ⟨ m, hm ⟩
    have tm : ∀ (p : ℕ), Nat.Prime p → p < m := by
        intro p hp
        have := hm p
        by_contra nn
        simp at nn
        exact (this nn) hp

    --have primeset : Finset ℕ := (Finset.range m).filter Nat.Prime
    have belong : ∀ p : ℕ, Nat.Prime p → p ∈ (Finset.range m).filter Nat.Prime := by
        intro pr hpr
        simp
        apply And.intro
        apply tm
        exact hpr
        exact hpr

    by_cases hmas : Nat.Prime (1 + ∏ k ∈ (Finset.range m).filter Nat.Prime, k)
    have yeah := belong (1 + ∏ k ∈ Finset.filter Nat.Prime (Finset.range m), k) hmas
    simp at yeah
    have : ∀ k ∈ Finset.filter Nat.Prime (Finset.range m), k ≠ ∏ j ∈ Finset.filter Nat.Prime (Finset.range m), j := by
        intro k hk
        simp at hk
        sorry
    sorry
    sorry
    /- have yeahno := yeah.left
    linarith
    sorry -/
