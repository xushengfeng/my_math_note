import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

open Set

variable {U : Type}

example (x : U) (A B : Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  exact h1 h2
