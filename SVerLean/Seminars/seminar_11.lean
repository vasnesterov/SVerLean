import Mathlib

open Filter Topology

-- Найдите точную нижнюю границу множества значений функции `5 * Real.sin x - 12 * Real.cos x`.
-- (ответ: `-13`)
example : IsGLB (Set.range (fun x ↦ 5 * Real.sin x - 12 * Real.cos x)) (-13) := by
  sorry

-- Докажите что функция `√x` равномерно непрерывна на множестве `[0, ∞)`.
example : UniformContinuousOn (fun (x : ℝ) ↦ √x) (Set.Ici 0) := by
  sorry

def A : Matrix (Fin 3) (Fin 2) ℝ := !![-1, 1; 2, -1; 2, -2]

def B : Matrix (Fin 2) (Fin 2) ℝ := !![-3, -3; 1, 1]

def C : Matrix (Fin 2) (Fin 3) ℝ := !![2, 2, 3; -1, -3, -2]

-- Докажите что детерминант `ABC` равен нулю.
example : (A * B * C).det = 0 := by
  sorry

-- Пусть `A` и `B` - матрицы размера `n × n` такие что `AB = BA`, `A³ = 0` и `B² = 0`.
-- Докажите что `(A + B)⁴ = 0`.
example (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
    (h1 : A * B = B * A)
    (h2 : A ^ 3 = 0)
    (h3 : B ^ 2 = 0) :
    (A + B) ^ 4 = 0 := by
  sorry

-- Пусть квадратная матрица `A` такова что `Aᵐ = 0` для некоторого `m`.
-- Покажите что `E - A` обратима.
example (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (h : A ^ m = 0) :
    IsUnit (1 - A) := by
  sorry

-- Пусть последовательность `(aₙ)` сходится к `c`.
-- Докажите что любая её перестановка также сходится к `c`.
example (a : ℕ → ℝ) (s : ℕ ≃ ℕ) (c : ℝ) (ha : Tendsto a atTop (𝓝 c)) :
    Tendsto (a ∘ s) atTop (𝓝 c) := by
  sorry
