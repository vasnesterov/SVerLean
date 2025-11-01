import Mathlib

/- # calc-mode -/

example (f : ℕ → ℕ) (hf : ∀ x y, f (x + y) = f x + f y) : ∀ n, f n = (f 1) * n := by
  intro n
  induction n with
  | zero =>
    simp
    suffices f 0 = f 0 + f 0 by
      grind
    calc
      f 0 = f (0 + 0) := by
        simp
      f (0 + 0) = f 0 + f 0 := by
        apply hf
  | succ m ih =>
    rw [hf, ih]
    ring

/- # congr -/

example (f : ℤ → ℤ) (g : ℤ → ℤ) (hg : ∀ n, g (g n) = n) :
    f 4 = f (g (g 3) + 1) := by
  congr
  rw [hg]
  norm_num

/- # fun_induction -/

def fib (n : Nat) := match n with
  | 0 => 1
  | 1 => 1
  | m + 2 => fib m + fib (m + 1)

example (n : ℕ) : fib n ≤ 2 ^ n := by
  fun_induction fib n with
  | case1 => norm_num
  | case2 => norm_num
  | case3 m ih1 ih2 =>
    calc
      fib m + fib (m + 1) ≤ 2 ^ m + fib (m + 1) := by
        gcongr
      _ ≤ 2 ^ m + 2 ^ (m + 1) := by
        gcongr
      _ = 3 * 2 ^ m := by
        simp [pow_succ]
        ring
      _ ≤ 2 ^ (m + 2) := by
        simp [pow_succ]
        ring_nf
        gcongr
        norm_num


/- # induction ... generalizing -/

def fastFib (n : Nat) : Nat :=
  go 1 1 n
where go (x y : Nat) (stepsLeft : Nat) :=
  match stepsLeft with
  | 0 => x
  | stepsLeftNew + 1 =>
    go y (x + y) stepsLeftNew

theorem fastFib_go_eq_fibs (n stepsLeft : Nat) :
    fastFib.go (fib n) (fib (n + 1)) stepsLeft = fib (n + stepsLeft) := by
  induction stepsLeft with
  | zero =>
    simp [fastFib.go]
  | succ stepsLeftNew ih =>
    simp [fastFib.go]
    have h : fib n + fib (n + 1) = fib (n + 2) := rfl
    rw [h]
    rw [ih]
    sorry

theorem fastFib_go_eq_fibs' (n stepsLeft : Nat) :
    fastFib.go (fib n) (fib (n + 1)) stepsLeft = fib (n + stepsLeft) := by
  induction stepsLeft generalizing n with
  | zero =>
    simp [fastFib.go]
  | succ stepsLeftNew ih =>
    simp [fastFib.go]
    have h : fib n + fib (n + 1) = fib (n + 2) := rfl
    rw [h]
    rw [ih]
    congr 1
    ring

/- # induction ... using: другие индуктивные принципы -/

namespace hidden

def Prime (n : ℕ) : Prop :=
  n > 1 ∧ ∀ m, m ∣ n → (m = 1 ∨ m = n)

example (n : ℕ) (hn : 1 < n) : ∃ m : ℕ, Prime m ∧ m ∣ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
  by_cases h_prime : Prime n
  · use n
  simp [Prime] at h_prime
  specialize h_prime hn
  obtain ⟨k, hk⟩ := h_prime
  have hk1 : k < n := by
    suffices k ≤ n by omega
    apply Nat.le_of_dvd
    · omega
    · exact hk.left
  have hk2 : 1 < k := by
    suffices k ≠ 0 by omega
    intro hk0
    subst hk0
    simp at hk
    omega
  specialize ih k hk1 hk2
  obtain ⟨p, hp⟩ := ih
  use p
  constructor
  · exact hp.left
  · calc
      _ ∣ k := hp.right
      _ ∣ n := hk.left

/- # decide +native -/

example : ∃ n, n ≤ 10 ∧ ¬ Nat.Prime (2 ^ (2 ^ n) + 1) := by
  decide

-- `decide +native` вместо `redude (inst : Decidable p)`
-- делает `eval (inst : Decidable p)`. Поэтому он быстрее
-- но за это мы платим тем что теперь мы верим не только
-- ядру Lean, но еще и компилятору.
example : ∃ n, n ≤ 10 ∧ ¬ Nat.Prime (2 ^ (2 ^ n) + 1) := by
  decide +native

-- вообще верить компилятору приемлемо если мы занимаемся
-- верификацией кода который потом все равно компилируем
-- этим компилятором.
-- В других случаях этого лучше избегать.

/- # Индуктивные предикаты -/

inductive Bracket
| op
| cl

inductive CorrectBS : (List Bracket) → Prop
| empty : CorrectBS []
| append {left right : List Bracket}
  (h_left : CorrectBS left) (h_right : CorrectBS right) : CorrectBS (left ++ right)
| enclose {bs : List Bracket} (h : CorrectBS bs) : CorrectBS (.op :: bs ++ [.cl])

theorem correct_empty : CorrectBS [] := CorrectBS.empty

theorem correct_two : CorrectBS [.op, .cl] := CorrectBS.enclose correct_empty

example : CorrectBS [.op, .cl, .op, .cl] := CorrectBS.append correct_two correct_two

example (bs : List Bracket) (h : CorrectBS bs) : bs.length % 2 = 0 := by
  induction h with
  | empty => simp
  | @append left right h_left h_right ih_left ih_right =>
    simp
    omega
  | @enclose bs h ih =>
    simp
    omega

end hidden
