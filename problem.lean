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


lemma nooo {m : ℕ} : insert (m + 1) (Finset.Icc 0 m) = Finset.Icc 0 (m + 1) := by
  apply Nat.Icc_insert_succ_right ?h
  exact Nat.le_add_left 0 (m + 1)

#check Nat.Icc_succ_left



example (a b c d : ℕ) (h1 : a ≤ b + 1) (h2 : a ≠ b + 1) : a ≤ b := by
  refine Nat.le_of_lt_succ ?_
  exact Nat.lt_of_le_of_ne h1 h2

example (a b c d : ℕ) (h1 : a ≤ b) : a ≤ b + 1 := by
  exact Nat.le_add_right_of_le h1




theorem helper1 : (Finset.Icc 0 (m)) ∪ ({m + 1} : Finset ℕ) = (Finset.Icc 0 (m + 1)) := by
  refine Eq.symm ((fun {α} {s₁ s₂} => Finset.ext_iff.mpr) ?_)
  intro a
  apply Iff.intro
  intro hpre
  apply Finset.mem_union.mpr
  rw [or_comm]
  apply or_iff_not_imp_left.mpr
  intro hpre2

  #check Finset.mem_Icc
  rw [Finset.mem_Icc] at hpre
  rw [Finset.mem_Icc]
  apply And.intro
  exact hpre.left
  simp at hpre2
  refine Nat.le_of_lt_succ ?_
  exact Nat.lt_of_le_of_ne hpre.right hpre2

  intro hpre
  rw [Finset.mem_Icc]
  apply Finset.mem_union.mp at hpre
  rcases hpre with hp | hq
  rw [Finset.mem_Icc] at hp
  apply And.intro
  exact hp.left
  exact Nat.le_add_right_of_le hp.right

  simp at hq
  apply And.intro
  exact Nat.zero_le a
  exact Nat.le_of_eq hq




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



theorem Problem (a : ℕ → ℝ) (h0 : a 0 = - 1) (h : ∀ n ≥ 1, ∑ k in Finset.Icc 0 n, (a (n - k))/(k + 1) = 0) : ∀ n ≥ 1, a (n) ≥ 0 := by
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
    have hfin : a (m + 1) = ∑ k in Finset.Icc 0 m, (a (m - k))/((k + 1)*(k + 2)) := by
      have temp1 : (-1) * (m + 1) / (m + 2) * (a 0 / (m + 1)+ ∑ k in Finset.Icc 0 (m - 1), a (m - k) / (k + 1)) = (-1) * (m + 1)/(m + 2) * 0 := congrArg (fun x : ℝ => (-1) * (m + 1)/(m + 2) * x) hdope2
      rw [mul_zero] at temp1
      have hadded_term := Mathlib.Tactic.LinearCombination.add_pf hdope1 temp1

      sorry

    sorry

    -- case m=1, manual computaion
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
