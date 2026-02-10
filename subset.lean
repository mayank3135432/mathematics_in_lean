import Mathlib.Data.Set.Basic

variable {s : Set α}

theorem my_subset_tntersec_mono (h : s ⊆ t ) : (s ∩ u) ⊆ (t ∩ u) := by
  intro x -- turns subset to implication
  intro hx
  have hx_in_s := hx.left
  have hx_in_t := h hx_in_s
  --have hg := ⟨ hx_in_t , hx.right ⟩
  refine (Set.mem_inter_iff x t u).mpr ?_
  exact And.intro hx_in_t hx.right

theorem my_subset_tntersec_mono2 (h : s ⊆ t ) : (s ∩ u) ⊆ (t ∩ u) := by
  intro x -- turns subset to implication
  intro hx
  have hx_in_t := h hx.left
  exact (Set.mem_inter_iff x t u).mpr (And.intro hx_in_t hx.right)



#print Set.subset_inter


#check Set.mem_inter_iff

variable {s1 s2 : Set α}
#check s1 ⊆ s2
