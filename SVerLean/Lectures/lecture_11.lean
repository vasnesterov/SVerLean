import Mathlib

open Set Filter Topology

-- Правда ли что если `f` и `g` не имеют предела в точке `x`, то `f + g` не имеет предела в этой
-- точке? (ответ: нет)
example : ∃ (f g : ℝ → ℝ) (x : ℝ), ¬ ContinuousAt f x ∧ ¬ ContinuousAt g x ∧
    ContinuousAt (f + g) x := by
  sorry

def Equation (x : ℝ) : Prop := x ^ 5 - 3 * x = 1

-- Докажите что у уравнения `x ^ 5 - 3 * x = 1` есть три различных корня.
example : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ Equation x ∧ Equation y ∧ Equation z := by
  sorry

-- Найдите формулу для суммы кубов первых `n` натуральных чисел.
example (n : ℕ) : ∑ k ∈ Finset.range n, (k : ℕ) ^ 3 = (n * (n - 1) / 2) ^ 2 := by
  sorry

-- Покажите что последовательность `sin n` расходится
example (c : ℝ) : ¬ Tendsto (fun n ↦ Real.sin n) atTop (𝓝 c) := by
  sorry

noncomputable def x (n : ℕ) : ℝ := match n with
  | 0 => 13
  | n + 1 => √(12 + x n)

-- Докажите что последовательность `xₙ` сходится и найдите её предел.
example : Tendsto x atTop (𝓝 4) := by
  sorry

-- Рассмотрим пространство функций `ℝ → ℝ` как векторное пространство над полем `ℝ`.
-- Докажите что система функций `{1, sin x, sin² x, ..., sinⁿ x}` линейно независима.
example (n : ℕ) : LinearIndependent ℝ (fun (i : Fin n) ↦ fun (x : ℝ) ↦ (Real.sin x) ^ (i : ℕ)) := by
  sorry

-- Найдите сумму `arctg (k - 1) / (k ^ 3 - 1)` для `k` от `2` до `n`.
example (n : ℕ) :
    ∑ k ∈ Set.Icc 2 n, Real.arctan ((k - 1) / (k ^ 3 - 1)) =
    Real.arctan (n + 1) - Real.arctan 2 := by
  sorry
