import Mathlib


#check List.argmin_eq_none
#check Option.get
#check Option.isSome
#check Option.ne_none_iff_isSome
#check Finset.sort
#check Finset.mem_sort
#check Finset.sort_toFinset

-- The generic Mapcode (verified) structure, extending MapCodeUnverified [26, 27].
-- It includes components for formal verification: specification, bound function, invariant, and their proofs.
structure Mapcode (I : Type u) (A : Type v) (X : Type w) [DecidableEq X] where
  ρ : I → X
  F : X → X
  π : X → A
  f : I → A -- Specification map
  σ : X → Nat -- Bound function for termination
  θ : X → A -- Invariant function

  wf: -- Well-foundedness condition (proof that σ decreases) [14, 26]
    ∀ x : X, (F x ≠ x) → σ (F x) < σ x

  invariant : -- Invariant properties (initial, preservation, agreement at fixed points) [14, 26]
    (∀ i : I, θ (ρ i) = f i) -- Initial condition
    ∧ (∀ x : X, θ (F x) = θ x) -- Preservation
    ∧ (∀ x : X, (F x = x) → θ x = π x) -- Agreement at fixed points

namespace Mapcode
variable {I : Type u} {A : Type v} {X : Type w} [DecidableEq X]

-- `runTillFix` with invariant for verified Mapcode, returning the fixed point along with a proof of invariant preservation [14, 24].
def runTillFix (m : Mapcode I A X) (x : X) : {xFix: X // m.F xFix = xFix ∧ (m.θ xFix = m.θ x)} :=
  let x' := (m.F x)
  if hx : x' = x then
    ⟨ x, ⟨hx, rfl⟩ ⟩
  else
    let ⟨xf, ⟨hfix, hθ⟩⟩ := m.runTillFix x'
    ⟨xf, ⟨ hfix,
      hθ.trans (m.invariant.right.left x) ⟩⟩
  termination_by (m.σ x) -- Termination is guaranteed by the bound function σ [24, 28]
  decreasing_by
    simp
    apply m.wf
    intro h
    contradiction

-- `runWithProof` for verified Mapcode, returning a result along with a proof of its correctness [24, 28].
def runWithProof (m : Mapcode I A X) (i : I) : { a : A // a = m.f i } :=
  let x₀ := m.ρ i
  let ⟨ xout, ⟨hFix, hθ⟩ ⟩ := m.runTillFix x₀
  let result := m.π xout
  ⟨ result, by
    have hInit : m.θ x₀ = m.f i := by
      exact m.invariant.left i
    have hFix_prop : m.F xout = xout → m.θ xout = result := by
      apply m.invariant.right.right
    simp_all
  ⟩
end Mapcode

-- Primitives



def h_l (a : List ℕ) : List ℕ :=
  a.take ((a.length + 1) / 2)

def h_r (a : List ℕ) : List ℕ :=
  a.drop ((a.length + 1) / 2)

#eval h_l [1,2,3,4,5]  -- [1,2,3]
#eval h_r [1,2,3,4,5]  -- [4,5]

#eval [1,2,3,4,5] ≤ [5,2,3,4,5]
#eval [5,2,3,4,5] ≤ [1,2,3,4,5]
#eval [1,2,3,4] ≤ [1,2,3,4,5]
#eval h_l [1,2,3,4]    -- [1,2]
#eval h_r [1,2,3,4]    -- [3,4]

def htree (a : List ℕ) (n : ℕ) : Finset (List ℕ) :=
  if hn : n = 0 then {a}
  else by
    have setl := (htree a (n - 1)).image h_l
    have setr := (htree a (n - 1)).image h_r
    exact {a} ∪ setl ∪ setr
theorem arr_in_tree : ∀ (a : List ℕ) (n : ℕ) , a ∈ htree a n := by
  intro a n
  unfold htree
  split_ifs with hcond
  exact Finset.mem_singleton.mpr rfl
  refine Finset.mem_union_left (Finset.image h_r (htree a (n - 1))) ?_
  refine Finset.mem_union.mpr ?_
  refine Or.symm (Or.inr ?_)
  exact Finset.mem_singleton.mpr rfl
  -- `apply?` tactic carried me all the way
/-
theorem arr_child_in_tree_if_arr_in_tree : ∀ (a arr : List ℕ) (n : ℕ) , arr ∈ htree a n → (h_l arr) ∈ htree a (n + 1) ∧ (h_r arr) ∈ htree a (n + 1) := by
  intro a arr n harr
  constructor
  unfold htree
  split_ifs with hcond hn
  exact False.elim hn
  simp
  apply Or.inr
  apply Or.inl
  unfold htree

 -/

theorem left_child_in_tree_if_arr_in_tree : ∀ (a arr : List ℕ) (n : ℕ) , arr ∈ htree a n → (h_l arr) ∈ htree a (n + 1) := by
  sorry

#eval do
  let x := htree [1,2,3,4] 1
  IO.println (x.sort (fun a b => a ≤ b))
-- see, see, say you wanna see result with big lists at start and small at end
-- but to have the sort funcrtion do it is difficult. Must prove DecidableRel, isTrans and AntiSymm
-- to much effort for somethign only to make display prettier.
-- No actual effect on System
-- Can't I simply do it ?

#check Nat.clog

def I := List ℕ
def A := List ℕ
def X (a : I) := {b : List ℕ // b ∈ htree a (Nat.clog 2 a.length)} → Option (List ℕ)

def iρi {a : I} : I → X a := by
  intro
  exact fun _ => none
--def iπi {a : I} : X a → A := fun x => (x ⟨a , arr_in_tree a (Nat.clog 2 a.length)⟩)
/-
def iFi {a : I} : X a → X a := fun (x : Xa) => fun arr =>
  if arr.length ≤ 1 then arr
  else if  -/

--def merge (la : List ℕ) (lb : List ℕ) : List ℕ :=

#check List.cons
#check List.head

def isSorted (l : List ℕ) : Prop :=
  match l with
    | [] => True
    | a :: as =>  (isSorted as) ∧ (∀ x ∈ as, a ≤ x)

--def isSorted2 (l : List ℕ) : Prop :=


theorem tail_sorted (arr : List ℕ) : isSorted arr → isSorted (arr.tail) := by
  intro harr
  unfold isSorted at harr
  cases htail : arr with
    | nil =>
      unfold isSorted
      simp
    | cons a as =>
      simp [htail] at harr
      simp
      exact harr.left

#check List.tail
#eval [3,2,5,1].tail
#eval [3].tail
def emlis : List ℕ := []
#eval emlis.tail



/-
def foo (la : List ℕ) (lb : List ℕ) : List ℕ :=
  match la with
    | [] => lb
    | a_num :: atail => match lb with
      | [] => la
      | b_num :: btail => if a_num ≤ b_num then (a_num :: (foo atail lb)) else (b_num :: foo la btail)
  termination_by la.length + lb.length
     -/
    --apply List.length_tail_less
def foo (la : List ℕ) (lb : List ℕ) : List ℕ :=
  match la, lb with
  | [], _ => lb
  | _, [] => la
  | a :: as, b :: bs =>
    if a ≤ b then
      a :: foo as (b :: bs) -- 'as' is shorter than 'a::as'
    else
      b :: foo (a :: as) bs -- 'bs' is shorter than 'b::bs'


example (h1 : False) : 1=2 := by
  exact False.elim h1

theorem hfoo (la : List ℕ) (hla : isSorted la) (lb : List ℕ) (hlb : isSorted lb) : isSorted (foo la lb) := by
  unfold isSorted
  by_cases hasum : (foo la lb) = []
  simp [hasum]
  split
  rename_i ld hh
  exact False.elim (hasum hh)
  rename_i xx xs dd
  sorry

theorem hfoo2 (la : List ℕ) (hla : isSorted la) (lb : List ℕ) (hlb : isSorted lb) : isSorted (foo la lb) := by
  induction la
  unfold foo
  simp
  exact hlb
  rename_i a as tail_ih
  unfold isSorted at hla
  have fooaslb_sorted := tail_ih hla.left
  induction lb
  unfold foo
  unfold isSorted
  exact hla
  rename_i b bs bail_ih
  --unfold isSorted at hlb
  have := hlb.left
  apply bail_ih at this
  have : isSorted (foo as (b :: bs)) → isSorted (foo as bs) := by
    intro hnow
    unfold foo at hnow

    sorry

  sorry


theorem hfoo3 (la : List ℕ) (hla : isSorted la) (lb : List ℕ) (hlb : isSorted lb) : isSorted (foo la lb) := by
  induction la
  unfold foo
  simp
  exact hlb
  rename_i a as tail_ih
  unfold isSorted at hla
  have fooaslb_sorted := tail_ih hla.left
  unfold foo
  /-
  cases a::as
  simp
  exact hlb
  -/
  cases lb
  simp
  exact hla
  simp
  rename_i b bs

  split_ifs
  rename_i hcond
  unfold isSorted
  constructor
  exact fooaslb_sorted
  -- `x` either is in `as` or in `b::bs`
  -- case 1 , we have `a ≤ x` as `a::as` is sorted
  -- case 2 , we can show `b ≤ x` which via transitivity with  `a ≤ b` , we get `a ≤ x`
  sorry

  rename_i hcond
  unfold isSorted
  constructor

  induction bs
  unfold foo
  exact hla
  rename_i b' b's btail_ih

  sorry



  sorry
  --unfold foo

  /-
  cases as
  simp
  constructor
  exact hcond
  intro x hx
  have : b ≤ x := hlb.right x hx
  exact Nat.le_trans hcond this
  simp
  rename_i aa aas
  have : a ≤ aa := by
    have yo2 : aa ∈ aa::aas := List.mem_cons_self aa aas
    exact hla.right aa yo2 -/




theorem hfoo5 (la lb : List ℕ) (hla : isSorted la) (hlb : isSorted lb) : isSorted (foo la lb) := by
  induction la, lb using foo.induct
  rename_i x
  unfold foo
  simp
  exact hlb
  rename_i x hx
  unfold foo
  simp
  exact hla
  rename_i a as b bs h ih1
  unfold foo

  sorry

  sorry
