import Mathlib

variable {P Q R S T : Prop}

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  sorry

example : P ∧ Q → Q ∧ R → P ∧ R := by
  sorry

example : P ∨ False ↔ P ∧ True := by
  sorry

example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by
  sorry

example : ¬ ¬ ¬ False := by
  sorry

example : (P → Q) → ¬Q → ¬P := by
  sorry

/-- Комментарий: эта формула называется "закон Пирса". Это пример тавтологии,
которая содержит только импликацию, но при этом не доказуема без
исключенного третьего. -/
example : ((P → Q) → P) → P := by
  by_cases hP : P <;> by_cases hQ : Q <;> sorry
