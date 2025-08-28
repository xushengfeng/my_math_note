variable (x1 x2 : Prop)

-- add x
example (h : x1 ∧ x2) : x1 := by
  exact h.left

example (h : x1 ∧ x2) : x2 := by
  exact h.right

-- add add

example (h1 : x1) (h2 : x2) : x1 ∧ x2 :=by
  apply And.intro
  · exact h1
  · exact h2

-- or x

example (p : Prop) (h1 : x1 → p) (h2 : x2 → p) (h : x1 ∨ x2) : p :=by
  rcases h with a|b
  · exact h1 a
  · exact h2 b

-- or add
example (h1 : x1) : x1 ∨ x2 :=by
  apply Or.inl
  exact h1

example (h2 : x2) : x1 ∨ x2 :=by
  apply Or.inr
  exact h2

-- imp x

example (h : x1 → x2) (h1 : x1) : x2 :=by
  exact h h1

-- imp add
example (h : x2) : x1 → x2 :=by
  intro h1
  exact h

-- iff x
example (h : x1 ↔ x2) (h1 : x1) : x2 :=by
  exact h.mp h1

example (h : x1 ↔ x2) (h2 : x2) : x1 :=by
  exact h.mpr h2


-- iff add
example (h1 : x1) (h2 : x2) : x1 ↔ x2:=by
  apply Iff.intro
  · intro hx1
    exact h2
  · intro hx2
    exact h1
