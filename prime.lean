import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorial.Basic

#check Nat.Prime



theorem there_inf_prime_help : ∀ N : ℕ, 1 < N → ∃ p ≥ N, Nat.Prime p := by
  intro N
  intro hN
  let M := Nat.factorial N + 1
  let pr := M.minFac

  have Mneq1 : M > 1 := by
    apply Nat.lt_add_right 1 ?h
    exact Nat.one_lt_factorial.mpr hN

  have h : pr.Prime := by
    apply Nat.minFac_prime ?_ -- pr is minFac which has to be prime
    exact Ne.symm (Nat.ne_of_lt Mneq1) -- thx apply?

  use pr
  constructor -- to split AND Left Rightz
  -- if pr < N then pr divides M as M is factorial of N
  by_contra hn
  apply Nat.gt_of_not_le at hn
  have h₁ : pr ∣ M := by
    exact Nat.minFac_dvd M
  have h₂ : pr ∣ N.factorial := by
    apply Nat.dvd_factorial ?_ ?_
    exact Nat.minFac_pos M -- 0 < p
    exact Nat.le_of_succ_le hn -- < implies <=
  have h₃ : pr ∣ 1 := by -- bruh wut
    exact (Nat.dvd_add_iff_right h₂).mpr h₁
  apply Nat.eq_one_of_dvd_one at h₃
  apply Nat.not_prime_one
  rw [h₃] at h
  exact h
  /- have hnf : pr < N := by
   exact Nat.gt_of_not_le hn -/

  exact h


theorem there_inf_prime : ∀ N : ℕ, ∃ p ≥ N, Nat.Prime p := by
  intro N
  cases N
  case zero => -- case N=0
    use 2
    constructor
    -- sorry
    exact Nat.zero_le 2 -- thx lean
    exact Nat.prime_two -- thx lean
  case succ n =>
    cases n
    case zero => -- case N=1
      rw [zero_add]
      use 2
      constructor
      exact Nat.le_of_ble_eq_true rfl -- thx apply?
      exact Nat.prime_two -- thx apply?
    case succ m =>
      apply there_inf_prime_help (m + 1 + 1) ?_
      rw [add_assoc, one_add_one_eq_two]
      exact Nat.one_lt_succ_succ m
