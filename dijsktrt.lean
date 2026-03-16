import Mathlib


#check List.argmin_eq_none
#check Option.get
#check Option.isSome
#check Option.ne_none_iff_isSome
#check Finset.sort
#check Finset.mem_sort
#check Finset.sort_toFinset


def argminFinset [DecidableEq α] [LinearOrder α] (s : Finset α) (hne : s.Nonempty) (f : α → ℕ) : α := by
  have list_ne : (Finset.sort (fun a b => a ≤ b) s) ≠ [] := by
    rw [←Finset.sort_empty (fun a b => a ≤ b)]
    apply Finset.Nonempty.ne_empty at hne
    by_contra nn
    have : (Finset.sort (fun a b => a ≤ b) s).toFinset = (Finset.sort (fun a b => a ≤ b) ∅).toFinset := by
      exact congrArg List.toFinset nn -- idk what this is but okay. thanks `apply?`
    rw [s.sort_toFinset (fun a b => a ≤ b)] at this
    rw [Finset.sort_toFinset (fun a b => a ≤ b) ∅] at this
    exact hne this
  have : List.argmin f (Finset.sort (fun a b => a ≤ b) s) ≠ none := by
    by_contra nn
    rw [List.argmin_eq_none] at nn
    exact list_ne nn
  exact Option.get (List.argmin f ((s.sort (fun a b => a ≤ b)))) (Option.ne_none_iff_isSome.mp this)

theorem hargminFinset [DecidableEq α] [LinearOrder α] (s : Finset α) (hne : s.Nonempty) (f : α → ℕ) : ∀ xn ∈ s, f (argminFinset s hne f) ≤ f xn:= by
  intro x hx
  unfold argminFinset
  simp
  rw [←Finset.mem_sort (fun a b => a ≤ b)] at hx
  rw [←not_lt]

  apply List.not_lt_of_mem_argmin hx
  exact
    Option.get_mem
      (argminFinset.proof_8 s f (argminFinset.proof_4 s f (argminFinset.proof_3 s hne))) -- thx `apply?`

theorem h2argminFinset [DecidableEq α] [LinearOrder α] (s : Finset α) (hne : s.Nonempty) (f : α → ℕ) : (argminFinset s hne f) ∈ s:= by
  unfold argminFinset
  simp
  rw [←Finset.mem_sort (fun a b => a ≤ b)]
  apply List.argmin_mem (β := ℕ) (f := f)
  exact
    Option.get_mem
      (argminFinset.proof_8 s f (argminFinset.proof_4 s f (argminFinset.proof_3 s hne))) -- thanks apply?


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


structure Graph where
  V  : Finset ℕ
  E  : Finset { p : ℕ × ℕ // p.1 ∈ V ∧ p.2 ∈ V }
  wt : V × V → ℕ

def update (Gr : Graph) (d : Gr.V → ℕ) (U : Finset ℕ) (u : Gr.V) : Gr.V → ℕ := by
  -- apparantely (UsubV : U ⊆ Gr.V) is not necassary ryt now
  intro w
  if w.val ∈ U then
    exact Nat.min ((d u) + (Gr.wt (u,w))) (d w)
  else
    exact d w

-- dependent structure
structure I where
  Gr : Graph
  start  : {ps : ℕ // ps ∈ Gr.V}
  --h  : s ∈ Gr.V


structure A (Intro : I) where
  distances : Intro.Gr.V → ℕ

structure X (Intro : I) where
  Unvisisted :  Finset {v // v ∈ Intro.Gr.V}
  distances : Intro.Gr.V → ℕ
deriving DecidableEq


variable {i : I}

--def myMapcode : Mapcode I A (X problem) where
def iρi : I → (X i) := by
  intro
  have initX : (X i) := {
    Unvisisted := i.Gr.V.attach
    distances := by
      intro xx
      exact if xx = i.start then 0 else 99
  }
  exact initX

def iπi : (X i) → (A i) := by
  intro state
  have ans : (A i) := {
    distances := state.distances
  }
  exact ans


#check Finset.nonempty_iff_ne_empty
#check Finset.Nonempty.to_subtype
#check Finset.map
#check Function.argmin


def iFi : (X i) → (X i) :=
  fun x =>
    if h : x.Unvisisted = ∅ then x
    else by
      have dd : { v // v ∈ x.Unvisisted } → ℕ := by
        intro vv
        exact x.distances vv.val
      have : Nonempty x.Unvisisted := by
        have := ((x.Unvisisted).nonempty_iff_ne_empty).mpr h
        exact Finset.Nonempty.to_subtype this
      --let w := (x.Unvisisted).fold (fun a b => if x.distances a ≤ x.distances b then a else b) hne.some
      have ww := argminFinset (x.Unvisisted) (((x.Unvisisted).nonempty_iff_ne_empty).mpr h) (x.distances)
      have U' := x.Unvisisted.erase ww
      have d' := update i.Gr x.distances (U'.image Subtype.val) (ww)
      exact {
        Unvisisted := U'
        distances := d'
      }

def iσi : (X i) → ℕ := by
  intro xi
  exact xi.Unvisisted.card

#check Finset.card_lt_card

def iwfi : ∀ x : (X i), (iFi x ≠ x) → iσi (iFi x) < iσi x := by
  intro x
  intro hneq
  --unfold iFi
  unfold iσi
  unfold iFi
  simp
  by_cases hn : x.Unvisisted = ∅
  simp [hn] -- this will resolve the if-else
  unfold iFi at hneq
  simp [hn] at hneq -- this will resolve the if-else

  simp [hn] -- this will resolve the if-else
  apply Finset.card_lt_card
  refine Finset.erase_ssubset ?_ -- thank you `apply` <3
  exact h2argminFinset x.Unvisisted (Finset.nonempty_iff_ne_empty.mpr hn) x.distances


def iθi (x : X i) : (A i) :=
  if heq : x = iFi x then iπi x
  else iθi (iFi x)
  termination_by (iσi x)
  decreasing_by
    simp
    apply iwfi
    simp
    exact fun a => heq (id (Eq.symm a))

def ifi (i : I) : (A i) := iθi (iρi i)


-- please split this up and redo later
def invariant :
    (∀ i : I, iθi (iρi i) = (fun _ => ifi i) i)
    ∧ (∀ x : X i, iθi (iFi x) = iθi x)
    ∧ (∀ x : X i, (iFi x = x) → iθi x = iπi x) := by
  constructor
  intro ii
  rfl
  constructor
  intro x
  unfold iθi
  by_cases hh : x = iFi x
  have heq2 : iFi x = iFi (iFi x) := by
    exact congrArg iFi hh
  rw [dif_pos]
  rw [dif_pos]
  nth_rewrite 2 [hh]
  rfl
  nth_rewrite 1 [hh]
  rfl
  nth_rewrite 1 [hh]
  rfl
  split_ifs with hcond
  unfold iθi
  split_ifs
  rfl
  unfold iθi

  /- split
  unfold iθi
  split_ifs
  rfl
 -/

  -- screw my life, gotta do induction

  sorry
  intro x hx
  unfold iθi
  split_ifs with hcond
  rfl
  have := hcond (Eq.symm hx)
  cases this

  --unfold iθi

  /-
  refine
    dite_congr ?_ (fun h => congrArg iπi (id (Eq.symm hh))) fun h => congrArg iθi (id (Eq.symm heq))
  exact Eq.propIntro (fun a => hh) (congrArg iFi)
  refine dite_congr ?_ (fun h => congrArg iπi (id (Eq.symm h))) ?_
   -/

def invariant_first : (∀ i : I, iθi (iρi i) = (fun _ => ifi i) i) := by
  intro ii
  rfl


def invariant_end : (∀ x : X i, (iFi x = x) → iθi x = iπi x) := by
  intro x hx
  unfold iθi
  split_ifs with hcond
  rfl
  have := hcond (Eq.symm hx)
  cases this

def invariant_mid : (∀ x : X i, iθi (iFi x) = iθi x) := by
  intro x
  nth_rewrite 2 [iθi]
  split_ifs with hcond
  rw [← hcond]
  nth_rewrite 1 [iθi]
  apply if_pos hcond
  rfl


def MyMapcode : Mapcode (I) (A i) (X i) := {
  ρ := iρi
  F := iFi
  π := iπi
  f := fun _ => ifi i
  σ := iσi
  θ := iθi
  wf := iwfi
  invariant := sorry
}



def setgen (F : (X i) → (X i)) (y : X i) : Finset (X i) :=
  if h : y = F y then {y}
  else {y} ∪ setgen F (F y)
  termination_by (iσi y)
  decreasing_by
    simp
    apply iwfi
