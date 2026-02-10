import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

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

end MyGroup

end
