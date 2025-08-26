open Set

theorem Subset.trans {A B C : Set U} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
    intro x
    intro
    have h3:x∈ B:=h1 a
    exact h2 h3
