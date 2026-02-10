import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro hh
  rcases hh with ⟨q, hq⟩
  unfold FnLb at hq
  have koh := h q
  rcases koh with ⟨k, kohkk⟩
  have hk := hq k
  linarith

example : ¬FnHasUb fun x ↦ x := by
  intro conth
  unfold FnHasUb at conth
  rcases conth with ⟨c, ch⟩
  unfold FnUb at ch
  dsimp at ch
  have chc := ch (c + 1)
  linarith

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  unfold Monotone at h
  have hab := @h a b -- I still do not know what "@" does ):
  --apply lt_of_not_ge
  sorry



example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  sorry

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    unfold Monotone
    intro aa bb
    simp
  have h' : f 1 ≤ f 0 := le_refl _
  have hf := @h f monof 1 0 h'-- waht does @ do ?
  linarith


example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro hx
  have := @h x hx
  linarith

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  by_contra h'
  apply h' -- apply {P → Q} to goal Q gives you goal P
  intro x
  intro Px
  have existxPx : ∃ x, P x := Exists.intro x Px
  /- alternate, how I first thought about it
  have existxPx : ∃ x, P x := by use x
  -/
  exact h existxPx

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  by_contra h'
  -- no need to explicitly type x as α for prop P only takes in objects of type α
  rcases h' with ⟨x, hx⟩
  exact h x hx

theorem helper_hive (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  by_contra h'
  apply h' -- apply {P → Q} to goal Q gives you goal P
  intro x
  intro Px
  have existxPx : ∃ x, P x := Exists.intro x Px
  /- alternate, how I first thought about it
  have existxPx : ∃ x, P x := by use x
  -/
  exact h existxPx



example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply helper_hive at h'
  have hh : ∀ (x : α), P x := by
    intro xx
    have hhh := h' xx
    by_contra hnh
    exact hhh hnh
  exact h hh

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro hq
  rcases h with ⟨y, hy⟩
  apply hy (hq y)

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

theorem helper_hive2 (W : Prop) : ¬¬W ↔ W := by
  apply Iff.intro
  intro h
  by_contra nW
  exact h nW
  intro h
  by_contra nW
  exact nW h

example (h : ¬¬Q) : Q := by
  by_contra nW
  exact h nW

example (h : Q) : ¬¬Q := by
  by_contra nW
  exact nW h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  unfold FnHasUb at h
  unfold FnUb at h
  push_neg at h
  exact h

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  unfold Monotone at h
  push_neg at h -- OP strat
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
