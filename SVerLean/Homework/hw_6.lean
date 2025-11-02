import Mathlib

/- # Задача 1. Бинарный поиск -/

/-- Проверяет есть ли в векторе `vec` элемент `x`. В этой функции мы
*предполагаем* что список отсортирован, но не добавляем это как
Prop-аргумент функции. Это общая философия Lean/Mathlib: если
для функции Prop-аргументы не требуются, их туда и не добавляют.
Зато их добавляют в теоремы (как ниже). То есть функцию можно запустить
на "некорректном" входе, но для доказательств мы накладываем
требование корректности на вход. -/
def Vector.sortedContains {n : Nat} (vec : Vector Int n) (x : Int) : Bool :=
  match n with
  | 0 => false
  | m + 1 => go vec 0 ⟨m, by grind⟩
where
  go {m : Nat} (vec : Vector Int (m + 1)) (left right : Fin (m + 1)) : Bool :=
    if right.val - left.val ≤ 1 then
      if left == x then
        true
      else
        false
    else
      let middle : Fin (m + 1) := ⟨(left.val + right.val) / 2, by grind⟩
      if vec[middle] ≤ x then
        go vec middle right
      else
        go vec left middle
  termination_by right.val - left.val
  decreasing_by all_goals grind

/-- Если вектор, то в нем есть элемент `x` тогда и только тогда, когда
наша функция возвращает `true`. -/
theorem Vector.sortedContains_correct {n : Nat} {vec : Vector Int n} {x : Int}
    (h : ∀ i j : Fin n, i < j → vec[i] ≤ vec[j]) -- вектор отсортирован
    :
    (∃ i : Fin n, vec[i] = x) ↔
    Vector.sortedContains vec x = true := by
  sorry

namespace hidden

/- # Задача 2. Достижимость на графе

Пусть дан ориентированный граф `g` и пара вершин `u` и `v`.
Нужно проверить что из `u` в `v` есть путь.

В этой задаче предлагается верифицировать алгоритм такой проверки.

Алгоритм следующий:
```py
  # проверяет что есть путь из u в v, все внутренние вершины которого имеют
  # номер меньше k
  def isConnectedBelow(graph, k, u, v):
    if u == v:
      return True
    elif (u, v) in graph:
      return True
    elif k == 0:
      return False
    elif isConnectedBelow(graph, k - 1, u, v):
      return True
    return isConnectedBelow(graph, k - 1, u, k) and isConnectedBelow(graph, k - 1, k, v)

  def isConnected(graph, u, v):
    return isConnectedBelow(graph, graph.size, u, v)
```
По сути это алгоритм Флойда, только без расстояний.
-/

structure Graph where
  nVertices : ℕ
  edges : Array ( (Fin nVertices) × (Fin nVertices) )

inductive Connected (g : Graph) : Fin g.nVertices → Fin g.nVertices → Prop
| self (v : Fin g.nVertices) : Connected g v v
| edge {u v : Fin g.nVertices} (h : (u, v) ∈ g.edges) : Connected g u v
| trans {u v w : Fin g.nVertices} (huv : Connected g u v)
    (hvw : Connected g v w) : Connected g u w

/-- Существует путь из `u` в `v`, все внутренние вершины которого меньше `j`. -/
inductive ConnectedBelow (g : Graph) (j : ℕ) : Fin g.nVertices → Fin g.nVertices → Prop
| self (v : Fin g.nVertices) : ConnectedBelow g j v v
| edge {u v : Fin g.nVertices} (h : (u, v) ∈ g.edges) : ConnectedBelow g j u v
| trans {u v w : Fin g.nVertices} (huv : ConnectedBelow g j u v)
    (hvw : ConnectedBelow g j v w) (hv : v.val < j) : ConnectedBelow g j u w

theorem ConnectedBelow_mono {g : Graph} {j : ℕ} {u v : Fin g.nVertices}
    (h : ConnectedBelow g j u v) : ConnectedBelow g (j + 1) u v := by
  sorry -- разминка 😉

instance decideConnectedBelow (g : Graph) (j : ℕ) (u v : Fin g.nVertices) :
    Decidable (ConnectedBelow g j u v) :=
  match j with
  | 0 =>
    if h_eq : u = v then
      .isTrue (by
        sorry
      )
    else if h_edge : (u, v) ∈ g.edges then
      .isTrue (by
        sorry
      )
    else
      .isFalse (by
        sorry
      )
  | k + 1 =>
    if h1 : (decideConnectedBelow g k u v).decide then
      .isTrue (by
        sorry
      )
    else if hk : k ≥ g.nVertices then
      .isFalse (by
        sorry
      )
    else if h2 : (decideConnectedBelow g k u ⟨k, by simpa using hk⟩).decide &&
        (decideConnectedBelow g k ⟨k, by simpa using hk⟩ v).decide then
      .isTrue (by
        sorry
      )
    else
      .isFalse (by
        sorry -- ☠️
      )

instance (g : Graph) (u v : Fin g.nVertices) :
    Decidable (Connected g u v) :=
  if h : ConnectedBelow g g.nVertices u v then
    .isTrue (by
      sorry
    )
  else
    .isFalse (by
      sorry
    )

abbrev exampleGraph : Graph where
  nVertices := 6
  edges := #[(0, 1), (1, 2), (2, 0), (3, 0), (2, 4)]

#eval Connected exampleGraph 0 2

abbrev exampleGraph' : Graph where
  nVertices := 30
  edges := Array.ofFn (fun (i : Fin 29) => (i.castSucc, i.succ))

-- к сожалению алгоритм слишком медленный чтобы его запускать на чем-то
-- кроме крошечных графов
-- #eval Connected exampleGraph' 0 20

-- **Бонус**: реализуйте инстанс `Decidable (Connected g u v)`, работающий за
-- полиномиальное время, в идеале -- за линейное

end hidden
