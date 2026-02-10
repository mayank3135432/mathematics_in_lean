import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

-- Ring is (X,+,*) with assoc, dist and also (X,+) is a group
section
variable (R : Type*) [Ring R]
variable (Rxx : Type*) [Semiring Rxx]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_right_neg, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  -- intro new var h1 to add stuff on BOTH sides
  have h1 : -a + (a + b) = -a + (a + c) := by rw [h]
  rw [←add_assoc (-a) a b, ←add_assoc (-a) a c] at h1
  rw [neg_add_cancel] at h1
  rw [zero_add, zero_add] at h1
  exact h1

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [add_comm a b, add_comm c b] at h
  apply add_left_cancel at h
  exact h

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add]
    rw [add_zero]
    rw [add_zero]
  rw [add_left_cancel h] -- add_left_cancel by itself is not a eq
  -- but add_left_cancel h is

theorem zero_mul (a : R) : 0 * a = 0 := by -- my stuff
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← right_distrib] --heh heh new stuff
    rw [add_zero, add_zero]
  exact add_left_cancel h


theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by --done
  have ho : 0 + -a = a + b + -a := by
    rw [h]
  rw [zero_add, add_assoc, add_comm b (-a), ←add_assoc, add_comm a (-a), neg_add_cancel, zero_add] at ho
  exact ho

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by --done
  rw [add_comm] at h
  apply neg_eq_of_add_eq_zero at h
  rw [h]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  have hh : a + -a = 0 := by
    rw [add_comm, neg_add_cancel]
    -- a = --a
  have qq := eq_neg_of_add_eq_zero hh
  nth_rw 2 [qq]

end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]



theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg a a, add_comm, neg_add_cancel]



theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  have h : (1 + 1) * a = a + a := by
    rw [add_mul]
    rw [one_mul]
  rw [one_add_one_eq_two] at h
  exact h


end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G] -- multiplicative group

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

--theorem invinv (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by

-- ooff this one took lot of effort
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by -- HARD
  have invinv : (a⁻¹)⁻¹ * 1 = a := by
    have h1 : (a⁻¹)⁻¹ * a⁻¹ = 1 := inv_mul_cancel a⁻¹
    have h2 : (a⁻¹)⁻¹ * a⁻¹ * a = 1 * a := by
      rw [h1]
    rw [one_mul] at h2
    rw [mul_assoc, inv_mul_cancel] at h2
    exact h2

  nth_rw 1 [←invinv]
  rw [mul_assoc, one_mul]
  exact inv_mul_cancel a⁻¹

theorem mul_one (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a, ←mul_assoc, mul_inv_cancel, one_mul]


theorem mulcancel (a b c : G) (h : a * b = a * c) : b = c := by
  have hh : a⁻¹ * a * b = a⁻¹ * a * c := by
    rw [mul_assoc, h, ←mul_assoc]
  rw [inv_mul_cancel, one_mul, one_mul] at hh
  exact hh

theorem mulcanceloth (a b c : G) (h : b * a = c * a) : b = c := by
  have hh : b * a * a⁻¹ = c * a * a⁻¹ := by
    rw [mul_assoc]
    rw [mul_inv_cancel]
    rw [←h]
    rw [mul_assoc]
    rw [mul_inv_cancel]

  rw [mul_assoc, mul_inv_cancel] at hh
  rw [mul_assoc, mul_inv_cancel] at hh
  rw [mul_one, mul_one] at hh
  exact hh

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h : (a * b)⁻¹ * a * b = b⁻¹ * a⁻¹ * a * b := by
    rw [mul_assoc, inv_mul_cancel]
    rw [mul_assoc b⁻¹] --idk how this works but I am thankful
    rw [inv_mul_cancel, mul_one, inv_mul_cancel]
  rw [mul_assoc (b⁻¹ * a⁻¹)] at h
  rw [mul_assoc] at h
  exact mulcanceloth (a * b) (a * b)⁻¹ (b⁻¹ * a⁻¹) h



end MyGroup

end
