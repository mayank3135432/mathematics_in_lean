
theorem and_assoccr (hpqr : (p ∧ q) ∧ r) : (p ∧ (q ∧ r)) :=
  have hp : p := hpqr.left.left
  have hq : q := hpqr.left.right
  have hr : r := hpqr.right
  And.intro hp (And.intro hq hr)

theorem and_assoccl (hpqr :p ∧ (q ∧ r)) : ((p ∧ q) ∧ r) :=
  have hp : p := hpqr.left
  have hr : r := hpqr.right.right
  have hq : q := hpqr.right.left
  And.intro (And.intro hp hq) hr


theorem and_assocc : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (and_assoccr)
    (and_assoccl)

theorem and_assoc_with_tactic : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  intro hpqr
  apply And.intro
  exact hpqr.left.left
  apply And.intro
  exact hpqr.left.right
  exact hpqr.right

  intro hpqr
  apply And.intro
  apply And.intro
  exact hpqr.left
  exact hpqr.right.left
  exact hpqr.right.right
