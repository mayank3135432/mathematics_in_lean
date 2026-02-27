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
      have ww := x.Unvisisted.min' (((x.Unvisisted).nonempty_iff_ne_empty).mpr h)
      have U' := x.Unvisisted.erase ww
      have d' := update i.Gr x.distances (U'.image Subtype.val) (ww)
      exact {
        Unvisisted := U'
        distances := d'
      }

/-
def argminFinset
  (s : Finset α)
  (hne : s.Nonempty)
  (f : α → ℕ)
  : α := s.fold (fun a b => if f a ≤ f b then a else b) hne.some
. -/
#check Finset.fold
#check Finset.toList
#check Finset.empty_toList
/-
def argminFinset (s : Finset α) (hne : s.Nonempty) (f : α → ℕ) : α := by
  classical
  have com : Std.Commutative fun a b => if f a ≤ f b then a else b := by
    constructor
    intro a b
    by_cases hmas : f a = f b

    sorry
  have ass :  Std.Associative fun a b => if f a ≤ f b then a else b := by
    sorry
  refine
    s.fold
      (fun a b => if f a ≤ f b then a else b)
      ?start
      ?proof
   -/
