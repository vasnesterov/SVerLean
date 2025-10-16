import Mathlib

/-
Замените `sorry` ниже на корректные доказательства. Можно пользоваться
только следующими тактиками:
* `intro`
* `exact`
* `apply`
* `cases'`
* `obtain`
* `constructor`
* `left`
* `right`
* `change`
* `exfalso`
* `by_cases`
* `trivial`
-/

variable {P Q R S T : Prop}

example (h1 : (Q → P) → P) (h2 : Q → R) (h3 : R → P) : P := by
  sorry

example : (P → P → False) → P → Q := by
  sorry

example : (¬Q → ¬P) → P → Q := by
  sorry

-- curry & uncurry
example : (P ∧ Q → R) ↔ (P → Q → R) := by
  sorry

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  sorry
