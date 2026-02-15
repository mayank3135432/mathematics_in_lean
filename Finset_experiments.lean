/-
Just a file tp practice using Finset
 -/



import Mathlib.Data.Nat.GCD.Basic
import MIL.Common

variable {α : Type*} (s : Finset ℕ) (f g : ℕ → ℝ) (n : ℕ)

#check Finset.sum s f
#check Finset.prod s f

open BigOperators
open Finset


#check ({1, 2, 3} : Finset ℕ).sum (fun x => x)


#eval ({1, 2, 3} : Finset ℕ).sum (fun x => 2*x)

example : s.sum f = ∑ k ∈ s, f k := by
  rfl

#check Finset.sum_disj_sum
#check Finset.sum_union

theorem obvsly {s1 s2 : Finset ℕ} (h1 : Disjoint s1 s2) : (s1 ∪ s2).sum f = (s1.sum f) + (s2.sum f) := by
  apply Finset.sum_union h1


#check Finset.sum_equiv
-- ι is {n : Nat // 0 < n}
-- κ is Nat
-- α is ℝ
-- I intend s to be Finset.Icc 1 m
-- and t to be Finset.Icc 0 (m - 1)
-- and e to be foo, the defined {n : Nat // 0 < n} ≃ ℕ
/- theorem offoo : ∑ x ∈ Finset.Icc 1 m, f x = ∑ k ∈ Finset.Icc 0 (m - 1), f (k + 1) := by
  apply Finset.sum_equiv
  intro i
  sorry -/

example {a : ℕ} (h : 1 ≤ a) : a - 1 + 1 = a := by
  exact Nat.sub_add_cancel h
--set_option pp.proofs true

example {y a : ℕ} (h : 1 ≤ a) : y ≤ a - 1 → y + 1 ≤ a:= by
  exact fun a_1 => Nat.add_le_of_le_sub h a_1


theorem offoohelpa (hm : m ≥ 1) : ∑ x ∈ (Finset.Icc 1 m).attach, f x = ∑ k ∈ (Finset.Icc 0 (m - 1)).attach, f (k.val + 1) := by

  apply Finset.sum_equiv
  case hst =>
    simp

  case e =>
    have lillith : ∀ x : { x // x ∈ Icc 1 m }, x.val - 1 ∈ Icc 0 (m - 1) := by
      intro x
      simp
      rw [Nat.sub_add_cancel hm]
      have := x.property
      simp at this
      exact this.right
    -- ↑y + 1 ∈ Icc 1 m
    have kinnith : ∀ y : { x // x ∈ Icc 0 (m - 1) }, y.val + 1 ∈ Icc 1 m := by
      intro y
      simp
      have := y.property
      simp at this
      apply fun a_1 => Nat.add_le_of_le_sub hm a_1
      exact this

    have fee : { x // x ∈ Icc 1 m } ≃ { x // x ∈ Icc 0 (m - 1) } := {
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






theorem death (hm : m ≥ 1) (ss : Finset ℕ) : ∑ x ∈ ss.attach, f x = ∑ x ∈ ss, f x := by
  exact sum_attach ss f

/-
theorem offoo (hm : m ≥ 1) : ∑ x ∈ (Finset.Icc 1 m), f x = ∑ k ∈ (Finset.Icc 0 (m - 1)), f (k + 1) := by
  have := sum_attach (Finset.Icc 1 m) f
  rw [← this]
  have := sum_attach (Finset.Icc 0 (m - 1)) (fun x => f (x + 1))
  rw [← this] -/




theorem offoohelpa_ultima (hm : m ≥ 1) : ∑ x ∈ (Finset.Icc 1 m), f x = ∑ k ∈ (Finset.Icc 0 (m - 1)), f (k + 1) := by
  have := sum_attach (Finset.Icc 1 m) f
  rw [← this]
  have := sum_attach (Finset.Icc 0 (m - 1)) (fun x => f (x + 1))
  rw [← this]

  apply Finset.sum_equiv
  case hst =>
    simp

  case e =>
    have lillith : ∀ x : { x // x ∈ Icc 1 m }, x.val - 1 ∈ Icc 0 (m - 1) := by
      intro x
      simp
      rw [Nat.sub_add_cancel hm]
      have := x.property
      simp at this
      exact this.right
    -- ↑y + 1 ∈ Icc 1 m
    have kinnith : ∀ y : { x // x ∈ Icc 0 (m - 1) }, y.val + 1 ∈ Icc 1 m := by
      intro y
      simp
      have := y.property
      simp at this
      apply fun a_1 => Nat.add_le_of_le_sub hm a_1
      exact this

    have fee : { x // x ∈ Icc 1 m } ≃ { x // x ∈ Icc 0 (m - 1) } := {
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








/-


def goo : { x // x ∈ Icc 0 (m - 1) } → ℕ := by
  #check m
  exact fun k => k.val + 1



theorem offoohelp (hm : m ≥ 1) : ∑ x ∈ (Finset.Icc 1 m).attach, f x = ∑ k ∈ (Finset.Icc 0 (m - 1)).attach, f (k.val + 1) := by
  #check (Finset.Icc 1 m).attach
  -- { x // x ∈ Icc 1 m }
  have efun : { x // x ∈ Icc 1 m } ≃ { x // x ∈ Icc 0 (m - 1) } := {
    toFun := by
      intro G
      have hoo : ∀ xx : { x // x ∈ Icc 1 m } , xx.val - 1 ∈ Icc 0 (m - 1) := by
        intro xx
        simp
        rw [Nat.sub_add_cancel hm]
        have := xx.property
        simp at this
        exact this.right

      have goo := hoo G
      exact ⟨G.val - 1, goo⟩


    invFun := fun y => ⟨y.val + 1, _⟩
  }

  have foo : {n : ℕ // 0 < n} ≃ ℕ := {
    toFun := fun x => x.val - 1
    invFun := fun y => ⟨y + 1, Nat.succ_pos y⟩
    left_inv := by
      unfold Function.LeftInverse
      intro hl
      dsimp
      ring_nf
      sorry


    right_inv := sorry
  }
  apply sum_equiv
 -/




/-
hpos2 : ∀ k ∈ Finset.Icc 0 (m - 1), 0 < a (m - k)
hpos3 : ∀ k ∈ Finset.Icc 0 (m - 1), 0 < (k + 1) * (k + 2)
hpos4 : ∀ k ∈ Finset.Icc 0 (m - 1), 0 < a (m - k) / ((↑k + 1) * (↑k + 2))
⊢ 0 < ∑ k ∈ Finset.Icc 0 (m - 1), a (m - k) / ((↑k + 1) * (↑k + 2))

-/

example (h1 : ∀ k ∈ s, f k > 0) : ∑ k ∈ s, f k > 0 := by
  apply Finset.sum_pos
  exact h1
  sorry

example (h1 : ∀ k ∈ s, f k > 0) : ∑ k ∈ s, f k + ∑ k ∈ s, g k = ∑ k ∈ s, (f k) + (g k)  := by
  refine sum_add_eq_sum_add_of_exists ?a ?ha ?h
  use n
  sorry
  sorry
