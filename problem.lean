/-
Problem from "Formalizing IMO Problems and Solutions in Isabelle/HOL" Section 3.1
https://arxiv.org/abs/2010.16015
Taken From IMO 2006 shortlist A2 (Algebra)
Informal proof at https://www.imo-official.org/problems/IMO2006SL.pdf
-/
/-
mostly done as of 2026-02-15
Algebric manipulation remains
 -/

import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
--import Mathlib

open BigOperators

#check Finset.induction

#eval ∑ i in Finset.range 5, i   -- 0 + 1 + 2 + 3 + 4 = 10
#eval ∑ i in Finset.Icc 1 (3), i

-- a helper funvtion for the below proof
theorem helper_split_sum (n m : ℕ) (h1 : 0 ≤ n) (h2 : n ≤ m) : (Finset.Icc 0 n) ∪ (Finset.Icc (n + 1) (m)) = (Finset.Icc 0 m) := by
  refine Eq.symm ((fun {α} {s₁ s₂} => Finset.ext_iff.mpr) ?_)
  intro a
  apply Iff.intro
  intro hpre
  apply Finset.mem_union.mpr
  rw [or_comm]
  apply or_iff_not_imp_left.mpr
  intro hpre2
  rw [Finset.mem_Icc] at hpre
  rw [Finset.mem_Icc]
  apply And.intro
  exact hpre.left
  simp at hpre2
  by_contra hn
  have : n < a := by
    exact Nat.gt_of_not_le hn
  have : n + 1 ≤ a := by
    exact this
  have := hpre2 this
  linarith

  intro hpre
  rw [Finset.mem_Icc]
  apply Finset.mem_union.mp at hpre
  rcases hpre with hp | hq
  rw [Finset.mem_Icc] at hp
  apply And.intro
  exact hp.left
  have := hp.right
  exact Nat.le_trans this h2

  simp at hq
  apply And.intro
  have : 0 ≤ n + 1 := by
    exact Nat.le_add_right_of_le h1
  exact Nat.le_trans this hq.left
  exact hq.right


example (m : ℕ) (h1 : m ≥ 1) (h1 : m ≤ m - 1) : False := by
  revert h1
  simp
  exact h1

example (m : ℕ) (h1 : m ≥ 1) : ¬ m ≤ m - 1 := by
  simp
  exact h1


-- a helper funvtion for the below proof, for change of variable of summation
theorem offoohelpa_ultima (hm : m ≥ 1) (f : ℕ → ℝ) : ∑ x ∈ (Finset.Icc 1 m), f x = ∑ k ∈ (Finset.Icc 0 (m - 1)), f (k + 1) := by
  have := Finset.sum_attach (Finset.Icc 1 m) f
  rw [← this]
  have := Finset.sum_attach (Finset.Icc 0 (m - 1)) (fun x => f (x + 1))
  rw [← this]

  apply Finset.sum_equiv
  case hst =>
    simp

  case e =>
    have lillith : ∀ x : { x // x ∈ Finset.Icc 1 m }, x.val - 1 ∈ Finset.Icc 0 (m - 1) := by
      intro x
      simp
      rw [Nat.sub_add_cancel hm]
      have := x.property
      simp at this
      exact this.right
    -- ↑y + 1 ∈ Icc 1 m
    have kinnith : ∀ y : { x // x ∈ Finset.Icc 0 (m - 1) }, y.val + 1 ∈ Finset.Icc 1 m := by
      intro y
      simp
      have := y.property
      simp at this
      apply fun a_1 => Nat.add_le_of_le_sub hm a_1
      exact this

    have fee : { x // x ∈ Finset.Icc 1 m } ≃ { x // x ∈ Finset.Icc 0 (m - 1) } := {
      toFun := fun x => ⟨x.val - 1, lillith x ⟩
    -- it seems all fields depend on each other
      invFun := fun y => ⟨y.val + 1, kinnith y ⟩
      left_inv := by
        unfold Function.LeftInverse
        intro xn
        dsimp
        apply Subtype.ext
        dsimp
        have := xn.property
        simp at this
        rw [Nat.sub_add_cancel this.left]
        -- some issue with placeholders when simp on xn.property before using Subtype
        -- https://chatgpt.com/share/698b37ac-775c-800c-bfa7-337f68b165c5

      right_inv := by
        unfold Function.RightInverse
        unfold Function.LeftInverse
        intro xn
        dsimp
      }
    exact fee

  intro i1
  simp
  have := i1.property
  simp at this
  rw [Nat.sub_add_cancel this.left]



theorem imo2006_shortlist_A2 (a : ℕ → ℝ) (h0 : a 0 = - 1) (h : ∀ n ≥ 1, ∑ k in Finset.Icc 0 n, (a (n - k))/(k + 1) = 0) : ∀ n ≥ 1, a (n) > 0 := by
  intro n hn

  induction' n using Nat.strong_induction_on with num ih
  cases num with
  | zero =>
    cases hn
  | succ m =>
    by_cases hmas : m ≥ 1
  -- crazy stuff happens when I leave at =

    have hdope1 : a (m + 1) + (a 0)/(m + 2) + ∑ k in Finset.Icc 0 (m-1), (a (m - k))/(k + 2) = 0 := by
      have h2 := h (m + 1) hn
      have hdisj : Disjoint (Finset.Icc 0 (m)) ({m + 1} : Finset ℕ) := by
        refine Finset.disjoint_singleton_right.mpr ?_
        simp


      have honion : (Finset.Icc 0 (m)) ∪ ({m + 1} : Finset ℕ) = (Finset.Icc 0 (m + 1)) := by
        have := helper_split_sum (m) (m + 1) (Nat.le_add_left 0 m) (Nat.le_add_right m 1)
        rw [Finset.Icc_self (m + 1)] at this
        exact this


      rw [←honion] at h2

      rw [Finset.sum_union hdisj] at h2

      have := helper_split_sum 0 m le_rfl m.zero_le
      rw [Finset.Icc_self 0] at this

      rw [← this] at h2
      rw [zero_add] at h2
      have : Disjoint {0} (Finset.Icc 1 m) := by
        refine Finset.disjoint_singleton_left.mpr ?_
        simp
      rw [Finset.sum_union this] at h2

      rw [Finset.sum_singleton (fun x => a (m + 1 - x) / (↑x + 1)) (m + 1)] at h2
      rw [Finset.sum_singleton (fun x => a (m + 1 - x) / (↑x + 1)) 0] at h2
      simp at h2
      rw [add_comm] at h2
      rw [Eq.symm
            (add_assoc (a 0 / (↑m + 1 + 1)) (a (m + 1))
              (∑ x ∈ Finset.Icc 1 m, a (m + 1 - x) / (↑x + 1)))] at h2
      rw [add_assoc ↑m (1 : ℝ) 1] at h2  -- apparantly, must 1 : ℝ
      rw [one_add_one_eq_two] at h2
      -- a 0 / (↑m + 2) + a (m + 1)
      rw [add_comm (a 0 / (↑m + 2)) (a (m + 1))] at h2

      --have offoo : ∑ x ∈ Finset.Icc 1 m, a (m + 1 - x) / (↑x + 1) = ∑ k ∈ Finset.Icc 0 (m - 1), a (m - k) / (↑k + 2) := by
      have := offoohelpa_ultima hmas (fun x => a (m + 1 - x) / (↑x + 1))
      rw [this] at h2
      simp at h2
      simpa [add_assoc, one_add_one_eq_two] using h2 -- idk what simpa and using is


    have hdope2 : (a 0)/(m + 1) + ∑ k in Finset.Icc 0 (m - 1),  (a (m - k))/(k + 1) = 0 := by
      have hdisj : Disjoint (Finset.Icc 0 (m - 1)) ({m} : Finset ℕ) := by
        refine Finset.disjoint_singleton_right.mpr ?_
        simp
        exact hmas


      have honion : (Finset.Icc 0 (m - 1)) ∪ ({m} : Finset ℕ) = (Finset.Icc 0 (m)) := by
        have := helper_split_sum (m - 1) (m) (Nat.le_add_left 0 (m - 1)) (Nat.sub_le m 1)
        /- have : m - 1 + 1 = m := by
          exact Nat.sub_add_cancel hmas -/
        rw [Nat.sub_add_cancel hmas] at this
        rw [Finset.Icc_self (m)] at this
        exact this
      have h2 := h (m) hmas
      rw [← honion] at h2

      --useless line, can remove it
      have : ∑ k ∈ Finset.Icc 0 (m - 1) ∪ {m}, a (m - k) / (↑k + 1) = (∑ k ∈ Finset.Icc 0 (m - 1), a (m - k) / (↑k + 1)) + (∑ k ∈ ({m} : Finset ℕ), a (m - k) / (↑k + 1)) := by apply Finset.sum_union hdisj
      --useless line, can remove it
      have : ∑ k ∈ {m}, a (m - k) / (↑k + 1) = a (m - m) / (m + 1) := by exact Finset.sum_singleton (fun x => a (m - x) / (↑x + 1)) m

      rw [Finset.sum_union hdisj] at h2
      rw [Finset.sum_singleton (fun x => a (m - x) / (↑x + 1)) m] at h2
      rw [Nat.sub_self m] at h2
      rw [add_comm] at h2
      exact h2

    --have helper : (m + 1) ≠ 0 := by exact Nat.not_eq_zero_of_lt hn
    have hfin : a (m + 1) = (1/(m + 2)) * ∑ k in Finset.Icc 0 (m - 1), (a (m - k))/((k + 1)*(k + 2)) := by -- stupid mistake, 0 to m-1, NOT 0 to m
      have temp1 : (-1) * (m + 1) / (m + 2) * (a 0 / (m + 1)+ ∑ k in Finset.Icc 0 (m - 1), a (m - k) / (k + 1)) = (-1) * (m + 1)/(m + 2) * 0 := congrArg (fun x : ℝ => (-1) * (m + 1)/(m + 2) * x) hdope2
      rw [mul_zero] at temp1
      have hadded_term := Mathlib.Tactic.LinearCombination.add_pf hdope1 temp1
      -- pure algebric manipulation
      simp at hadded_term
      simp [mul_add, Finset.mul_sum] at hadded_term
      simp [h0] at hadded_term
      --field_simp at hadded_tern
      have lgm : ((-1 : ℝ) + -↑m) / (↑m + 2) * (-1 / (↑m + 1)) = 1 / (↑m + 2) := by sorry
      sorry
    #check Nat.cast_le

    have hpos1 : (1 : ℝ) / (↑m + 2) > 0 := by
      apply div_pos
      simp
      have : 3 ≤ m + 2 := by
        exact Nat.le_add_of_sub_le hmas
      exact gt_of_ge_of_gt (mod_cast this) zero_lt_three -- mod_cast to cast as ℝ instead of ℕ
    have hpos2 : ∀ k : ℕ , k ∈ Finset.Icc 0 (m - 1) → 0 < a (m - k) := by
      intro knum hknum
      simp at hknum
      have m_minus_k_pos : m - knum ≥ 1 := by
        apply Nat.le_sub_of_add_le
        have := Nat.add_le_add_right hknum 1
        simp
        rw [Nat.sub_add_cancel hmas] at this
        rw [add_comm]
        exact this
      exact ih (m - knum) (Nat.sub_lt_succ m knum) m_minus_k_pos

    have hpos3 : ∀ k : ℕ , k ∈ Finset.Icc 0 (m - 1) → 0 < (k + 1) * (k + 2) := by
      intro knum hknum
      exact Nat.zero_lt_succ (((knum + 1).mul (knum + 1)).add knum)
    have hpos4 : ∀ k ∈ Finset.Icc 0 (m - 1), 0 < a (m - k) / ((↑k + 1) * (↑k + 2)) := by
      intro knum hknum
      apply div_pos
      exact hpos2 knum hknum
      exact (mod_cast hpos3 knum hknum)
    rw [hfin]
    apply mul_pos
    apply hpos1
    apply Finset.sum_pos
    exact hpos4
    simp -- I am not sure how simp did it but okay
    -- case neg
    -- ie case of m=1, manual computaion
    have : m = 0 := by
      exact Nat.eq_zero_of_not_pos hmas
    rw [this]
    rw [zero_add]
    have lg := h 1 NeZero.one_le
    have : Finset.Icc 0 1 = {0, 1} := by
      exact rfl
    rw [this] at lg
    simp at lg
    rw [h0] at lg
    ring_nf at lg
    by_contra
    linarith

example ( a b : ℝ) : a ≤ b ↔ b ≥ a := by
  exact ge_iff_le

example {a b : ℝ} : a > 0 → b > 0 → a / b > 0 := by
  intro a_1 a_2
  exact div_pos a_1 a_2

example {a b : ℝ} : a < b → b ≤ c → a < c := by
  intro h1 h2
  exact gt_of_ge_of_gt h2 h1

example {a b : ℝ} : a < b → b ≤ c → a < c := by
  intro h1 h2
  exact gt_of_ge_of_gt h2 h1


example : m ≥ 1 → m - 1 + 1 = m := by
  intro ha
  exact Nat.sub_add_cancel ha

example {a b : ℝ} : 0 < a → 0 < b → 0 < a / b := by
  intro h1 h2
  exact div_pos h1 h2

example {a b : ℝ} : 0 < a → 0 < b → 0 < a * b := by
  intro h1 h2
  exact mul_pos h1 h2


example (a b : ℝ) : a < b → a ≠ b := by
  intro h
  exact ne_of_lt h
