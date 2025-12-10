import Mathlib

open Std.Do


/- # Монады

Подробнее см. https://lean-lang.org/functional_programming_in_lean/Monads/#monads и дальше.

Функциональное программирование удобно для верификации, но неудобно для программирования:
нет изменяемых переменных, циклов, ранних выходов из функции (`return`), исключений, неясно как
работать с файлами и вводом-выводом. Кроме того даже если удается написать программу в
функциональном стиле, она может быть неэффективной по сравнению с императивной реализацией.

К нашему счастью, есть элегантный способ добавить все эти возможности в функциональный код и
"взять лучшее из обоих миров". Ключевой инструмент для этого -- монады.

Практически весь код на функциональных языках программирования, который реально используется,
использует монады.
-/

namespace hidden


/- ## Вводный пример

Рассмотрим следующую задачу:

    Реализовать функцию `sum257 ns`, которая суммирует второй, пятый и
    седьмой элементы списка `ns` натуральных чисел. Используйте `Option ℕ` для
    результата, чтобы если в списке меньше семи элементов, можно было вернуть
    `Option.none`.
-/

def nth {α : Type} : List α → Nat → Option α
  | [],      _     => Option.none
  | x :: _,  0     => Option.some x
  | _ :: xs, n + 1 => nth xs n

def sum257 (ns : List ℕ) : Option ℕ :=
  match nth ns 1 with
  | Option.none    => Option.none
  | Option.some n₂ =>
    match nth ns 4 with
    | Option.none    => Option.none
    | Option.some n₅ =>
      match nth ns 6 with
      | Option.none    => Option.none
      | Option.some n₇ => Option.some (n₂ + n₅ + n₇)

/- Код некрасивый из-за множества `match`.

Мы можем собрать всю некрасивость в одну функцию, которую назовём `connect`: -/

def connect {α : Type} {β : Type} :
  Option α → (α → Option β) → Option β
  | Option.none,   _ => Option.none
  | Option.some a, f => f a

def sum257Connect (ns : List ℕ) : Option ℕ :=
  connect (nth ns 1)
    (fun n₂ ↦ connect (nth ns 4)
       (fun n₅ ↦ connect (nth ns 6)
          (fun n₇ ↦ Option.some (n₂ + n₅ + n₇))))

/- Вместо того чтобы определять `connect` самим, мы можем использовать
предопределённую общую операцию `bind` из Lean. Мы также можем использовать
`pure` вместо `Option.some`: -/

#check Option.bind
#check bind
#check pure

def sum257Bind (ns : List ℕ) : Option ℕ :=
  Option.bind (nth ns 1)
    (fun n₂ ↦ .bind (nth ns 4)
       (fun n₅ ↦ .bind (nth ns 6)
          (fun n₇ ↦ pure (n₂ + n₅ + n₇)))) -- pure = Option.some

/- Используя `bind` и `pure`, `sum257Bind` не ссылается на
конструкторы `Option.none` и `Option.some`.

Синтаксический сахар:

    `ma >>= f` := `bind ma f` -/

def sum257Op (ns : List ℕ) : Option ℕ :=
  nth ns 1 >>=
    fun n₂ ↦ nth ns 4 >>=
      fun n₅ ↦ nth ns 6 >>=
        fun n₇ ↦ pure (n₂ + n₅ + n₇)

/- Синтаксический сахар:

    do
      let a ← ma
      t
    :=
    ma >>= (fun a ↦ t)

    do
      ma
      t
    :=
    ma >>= (fun _ ↦ t) -/

def sum257Dos (ns : List ℕ) : Option ℕ :=
  do
    let n₂ ← nth ns 1
    do
      let n₅ ← nth ns 4
      do
        let n₇ ← nth ns 6
        pure (n₂ + n₅ + n₇)

/- `do` можно объединять: -/

def sum257Do (ns : List ℕ) : Option ℕ := do
  let n₂ ← nth ns 1
  let n₅ ← nth ns 4
  let n₇ ← nth ns 6
  pure (n₂ + n₅ + n₇)

/- Получается совсем как в императивном стиле!


## Две операции и три закона

В примере выше мы полностью абстрагировались от `Option` при помощи `bind` и `pure`.
Оказывается этих двух операций достаточно для абстрагирования от любого сайд-эффекта
(исключения, изменяемое состояние, недетерминизм, и т.д.).

Математически это означает что `Option` является монадой.

В общем случае __монада__ — это конструктор типов `m : Type → Type`,
снабжённый двумя выделенными операциями:

    `pure {α : Type} : α → m α`
    `bind {α β : Type} : m α → (α → m β) → m β`

Для `Option`:

    `pure` := `Option.some`
    `bind` := `connect`

Интуитивно мы можем думать о монаде как о закрытом ящике.

* `pure` помещает данные в ящик. (`α → m α`)
* `bind` хитрее: `m α → (α → m β) → m β`. Он позволяет взять ящик (`m α`) и
преобразователь который из значения `α` создает ящик со значением типа `β`.
Мы можем положить этот преобразователь в ящик, он (внутри ящика) преобразует находящееся
там там значение и на выходе получаем новый ящик со значением типа `β`.

Нет общего способа извлечь данные из монады, т.е. получить `α` из `m α`.

Рассмотрим основные примеры монад:

Тип                   | Эффект
--------------------- | -------------------------------------------------------
`Id`                  | без эффектов
`Option`              | простые исключения
`Except ε`            | исключения типа `ε` (например если `ε = OSError` то это будут исключения типа "не удалось открыть файл" и т.п.)
`fun α ↦ σ → α × σ`  | изменяемое состояние типа `σ` (мутабельные переменные)
`StateM σ`
`fun α ↦ t → α`      | неизменяемая переменная типа `t` (например, конфиг)
`ReaderM t`
`fun α ↦ String × α` | добавление текстового вывода (например, для логирования)
`IO`                  | взаимодействие с операционной системой
`TacticM`             | взаимодействие с tactic state
`Set`                 | недетерминированное вычисление, возвращающее значения `α`

Все вышеперечисленные являются унарными конструкторами типов `Type → Type`.

Некоторые эффекты не являются вычислимыми (например, `Set α`). Тем не менее
они полезны для абстрактного моделирования программ в логике.

Монады позволяют нам писать императивный код в функциональных языках благодаря `do`-нотации.

Кроме того они поддерживают общие операции, такие как
`List.mapM {m : Type → Type} [Monad m] {α β : Type} : (α → m β) → List α → m (List β)`
которые работают единообразно для всех монад.
Операции `bind` и `pure` должны подчиняться трём законам.

1. `pure` слева может быть поглащен:

    do
      let a' ← pure a;
      f a'
  =
    f a

2. `pure` справа может быть поглащен:

    do
      let a ← ma
      pure a
  =
    ma

3. `bind` ассоциативен:

    do
      let b ←
        do
          let a ← ma
          f a
      g b
  =
    do
      let a ← ma
      let b ← f a
      g b


## Тайпкласс для монад

Законы выше объединяются в один тайпкласс `LawfulMonad`.
Есть отдельный тайпкласс `Monad` который не требует выполнения законов. -/

class LawfulMonad (m : Type → Type)
  extends Pure m, Bind m where
  pure_bind {α β : Type} (a : α) (f : α → m β) :
    (pure a >>= f) = f a
  bind_pure {α : Type} (ma : m α) :
    (ma >>= pure) = ma
  bind_assoc {α β γ : Type} (f : α → m β) (g : β → m γ)
      (ma : m α) :
    ((ma >>= f) >>= g) = (ma >>= (fun a ↦ f a >>= g))

/- Пошагово:

* Мы создаём структуру, параметризованную унарным конструктором типов `m`.

* Структура наследует поля и любой синтаксический сахар от структур,
  называемых `Bind` и `Pure`, которые предоставляют операции `bind` и `pure` на
  `m` и некоторый синтаксический сахар.

* Определение добавляет три поля к тем, которые уже предоставлены `Bind` и
  `Pure`, для хранения доказательств законов.

Чтобы создать экземпляр этого определения с конкретной монадой, мы должны
предоставить конструктор типов `m` (например, `Option`), операторы `bind` и
`pure`, а также доказательства законов.


## Без эффектов

Наша первая монада — это тривиальная монада `m := Id` (т.е., `m := (fun α ↦ α)`). -/

def Id.pure {α : Type} : α → Id α
  | a => a

def Id.bind {α β : Type} : Id α → (α → Id β) → Id β
  | a, f => f a

instance Id.LawfulMonad : LawfulMonad Id where
  pure       := Id.pure
  bind       := Id.bind
  pure_bind  := by
    intro α β a f
    rfl
  bind_pure  := by
    intro α ma
    rfl
  bind_assoc := by
    intro α β γ f g ma
    rfl

/- ## Базовые исключения

Как мы видели выше, тип опции предоставляет базовый механизм исключений. -/

def Option.pure {α : Type} : α → Option α :=
  Option.some

def Option.bind {α β : Type} :
  Option α → (α → Option β) → Option β
  | Option.none,   _ => Option.none
  | Option.some a, f => f a

instance Option.LawfulMonad : LawfulMonad Option where
  pure       := Option.pure
  bind       := Option.bind
  pure_bind  := by
    intro α β a f
    rfl
  bind_pure  := by
    intro α ma
    cases ma with
    | none   => rfl
    | some _ => rfl
  bind_assoc := by
    intro α β γ f g ma
    cases ma with
    | none   => rfl
    | some _ => rfl

def Option.throw {α : Type} : Option α :=
  Option.none

def Option.catch {α : Type} : Option α → Option α → Option α
  | Option.none,   ma' => ma'
  | Option.some a, _   => Option.some a


/- ## Мутабельное состояние

Монада `StateM` предоставляет абстракцию, соответствующую изменяемому
состоянию. Компилятор распознает эту монаду и при компиляции Lean в C использует
мутабельные переменные для реализации этой монады. В результате происходит меньше копирований
и мы получаем более эффективный код. -/

def StateM (σ α : Type) : Type :=
  σ → α × σ

def StateM.get {σ : Type} : StateM σ σ
  | s => (s, s)

def StateM.set {σ : Type} (s : σ) : StateM σ Unit
  | _ => ((), s)

def StateM.pure {σ α : Type} (a : α) : StateM σ α
  | s => (a, s)

def StateM.bind {σ : Type} {α β : Type} (ma : StateM σ α)
      (f : α → StateM σ β) :
    StateM σ β
  | s =>
    match ma s with
    | (a, s') => f a s'

/- `StateM.pure` похож на оператор `return`; он не изменяет состояние.

`StateM.bind` похож на последовательную композицию двух операторов относительно
состояния. -/

instance StateM.LawfulMonad {σ : Type} : LawfulMonad (StateM σ) where
  pure       := StateM.pure
  bind       := StateM.bind
  pure_bind  := by intro α β a f; rfl
  bind_pure  := by intro α ma; rfl
  bind_assoc := by intro α β γ f g ma; rfl

def maxs : List ℕ → StateM ℕ (List ℕ)
  | []      => pure []
  | n :: ns => do
    let prev ← StateM.get
    if n < prev then
      maxs ns
    else
      StateM.set n
      let ns' ← maxs ns
      pure (n :: ns')

#eval maxs [1, 2, 3, 2] 0
#eval maxs [1, 2, 3, 2, 4, 5, 2] 0


/- ## Недетерминизм

Монада множеств хранит произвольное, возможно бесконечное число значений `α`. -/

#check Set

def Set.pure {α : Type} : α → Set α
  | a => {a}

def Set.bind {α β : Type} : Set α → (α → Set β) → Set β
  | A, f => {b | ∃a, a ∈ A ∧ b ∈ f a}

instance Set.LawfulMonad : LawfulMonad Set where
  pure       := Set.pure
  bind       := Set.bind
  pure_bind  := by simp [Set.pure, Set.bind]
  bind_pure  := by simp [Set.pure, Set.bind]
  bind_assoc := by
    intro α β γ f g A
    simp [Set.bind]
    ext x
    aesop

/- `List.mapM` работает единообразно для всех монад. -/
def List.mapM {m : Type → Type} [Monad m] {α β : Type}
    (f : α → m β) :
  List α → m (List β)
  | []      => pure []
  | a :: as => do
    let b ← f a
    let bs ← List.mapM f as
    pure (b :: bs)

end hidden

/- # Конструкторы монад

Разные эффекты (обычно) можно смешивать: например, исключения и мутабельное состояние.
Реализовано это при помощи монадических конструкторов:
-/
#check OptionT
#check OptionT (StateM Nat) -- `OptionT` добавляет простые исключения в монаду `StateM Nat`
/- и так далее: -/
#check StateT
#check ReaderT
#check ExceptT

-- при этом для них синтезируются нужные классы
#synth LawfulMonad <| OptionT (StateM Nat)

/- # Больше do-нотации

do-нотация не только дает синтаксический сахар для `pure` и `bind`.
Рассмотрим примеры
-/

-- 1. Мы используем монаду Id без эффектов, просто чтобы иметь доступ к `do`-нотации
def countZeroes (arr : Array Int) : Id Nat := do
  let mut cnt := 0 -- 2. Мутабельная переменная
  for elem in arr do -- 3. Цикл `for` по элементам массива (благодаря классу ForIn)
    if elem == 0 then -- 4. `if` без `else`
      cnt := cnt + 1
  return cnt -- 5. return

-- обычно вместо `Id` в типе пишут `Id.run` перед `do`
def findFirstEven (arr : Array Int) : Option Int := Id.run do
  for elem in arr do
    if elem % 2 == 0 then
      return some elem -- 5. early return
  return none

-- пример выше можно переписать в монаде `Option`
def findFirstEven' (arr : Array Int) : Option Int := do
  for elem in arr do
    if elem % 2 == 0 then
      return elem
  failure

def countPosBeforeSeven (arr : Array Int) : Option Nat := do
  let mut cnt := 0
  for elem in arr do
    if elem ≤ 0 then
      continue -- 6. continue
    cnt := cnt + 1
    if elem == 7 then
      break -- 7. break
  pure cnt


/- ## Исключения -/

-- `String` - тип ошибок, `Unit` - для возвращаемого значения
-- `Unit` используют когда функция ничего не возвращает (как `void` в C)
-- но может иметь эффекты внутри монады
def checkAllPositive (arr : Array Int) : Except String Unit := do
  for elem in arr do
    if elem ≤ 0 then
      throw "Not all positive"

def computeSum (arr : Array Int) : Except String Int := do
  try
    checkAllPositive arr
    return arr.sum
  catch err =>
    throw s!"Failed with error: {err}"

/- ## Мутабельный стейт -/

structure Bank where
  userToBalance : Std.HashMap String Int
deriving Repr

abbrev BankM := StateM Bank

def getBalance (name : String) : BankM Int := do
  let state ← get -- один из методов StateM, получаем текущий стейт
  pure <| state.userToBalance.getD name 0

def putMoney (name : String) (money : Int) : BankM Unit := do
  let balance ← getBalance name
  let newBalance := balance + money
  let state ← get
  set {state with
    userToBalance := state.userToBalance.insert name newBalance} -- set обновляет стейт

def putMoney' (name : String) (money : Int) : BankM Unit := do
  let balance ← getBalance name
  let newBalance := balance + money
  modify (fun state => -- modify обновляет стейт на месте, т.е. переиспользует ту же память
    {state with
      userToBalance := state.userToBalance.insert name newBalance})

-- modify иногда эффективнее set, поэтому обычно стараются использовать его

def test : BankM Int := do
  putMoney "Alice" 30
  putMoney "Bob" 40
  putMoney "Alice" (-20)
  return ← getBalance "Alice"

-- чтобы запустить функцию из `StateM` нужно дать ей начальный стейт
#eval test.run' ⟨∅⟩
-- `run'` возвращает результат

-- еще есть метод `run` возвращающий пару (результат, итоговый стейт)
#eval test.run ⟨∅⟩

/- # Верификация монадических программ

Подробнее см. https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic
-/

def mySum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out

theorem mySum_correct (l : Array Nat) : mySum l = l.sum := by
  -- Focus on the part of the program with the `do` block (`Id.run ...`)
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  -- Break down into verification conditions
  mvcgen
  -- Specify the invariant which should hold throughout the loop
  -- * `out` refers to the current value of the `let mut` variable
  -- * `xs` is a `List.Cursor`, which is a data structure representing
  --   a list that is split into `xs.prefix` and `xs.suffix`.
  --   It tracks how far into the loop we have gotten.
  -- Our invariant is that `out` holds the sum of the prefix.
  -- The notation ⌜p⌝ embeds a `p : Prop` into the assertion language.
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  -- After specifying the invariant, we can further simplify our goals
  -- by "leaving the proof mode". `mleave` is just
  -- `simp only [...] at *` with a stable simp subset.
  all_goals mleave
  -- Prove that our invariant is preserved at each step of the loop
  case vc1 ih =>
    -- The goal here mentions `pref`, which binds the `prefix` field of
    -- the cursor passed to the invariant. Unpacking the
    -- (dependently-typed) cursor makes it easier for `grind`.
    grind
  -- Prove that the invariant is true at the start
  case vc2 =>
    grind
  -- Prove that the invariant at the end of the loop implies the
  -- property we wanted
  case vc3 h =>
    grind

def nodup (l : List Int) : Bool := Id.run do
  let mut seen : Std.HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

theorem nodup_correct (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · Invariant.withEarlyReturn
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun xs seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ xs.prefix) ∧ xs.prefix.Nodup⌝)
  with grind

structure Supply where
  counter : Nat

def mkFresh : StateM Supply Nat := do
  let n := (← get).counter
  modify fun s => { s with counter := s.counter + 1 }
  return n

def mkFreshN (n : Nat) : StateM Supply (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    acc := acc.push (← mkFresh)
  return acc.toList

theorem mkFreshN_correct (n : Nat) (s : Supply) : ((mkFreshN n).run' s).Nodup := by
  -- Focus on `(mkFreshN n).run' s`.
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_wp_run'_eq h
  -- Show something about monadic program `mkFresh n`.
  -- The `mkFreshN` and `mkFresh` arguments to `mvcgen` add to an
  -- internal `simp` set and makes `mvcgen` unfold these definitions.
  mvcgen [mkFreshN, mkFresh]
  invariants
  -- Invariant: The counter is larger than any accumulated number,
  --            and all accumulated numbers are distinct.
  -- Note that the invariant may refer to the state through function
  -- argument `state : Supply`. Since the next number to accumulate is
  -- the counter, it is distinct to all accumulated numbers.
  · ⇓⟨xs, acc⟩ state =>
      ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  with grind

@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄ := by
  -- Unfold `mkFresh` and blast away:
  mvcgen [mkFresh] with grind

#check SPred

@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  -- `mvcgen [mkFreshN, mkFresh_spec]` if `mkFresh_spec` were not
  -- registered with `@[spec]`
  mvcgen [mkFreshN]
  invariants
  -- As before:
  · ⇓⟨xs, acc⟩ state =>
      ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  with grind

theorem mkFreshN_correct_compositional (n : Nat) (s : Supply) :
    ((mkFreshN n).run' s).Nodup := by
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_wp_run'_eq h
  mvcgen

structure TwoVals where
  x : Nat
  y : Nat

def swap : StateM TwoVals Unit := do
  modify (fun ⟨x, y⟩ => ⟨y, x⟩)

@[spec]
theorem swap_spec (a b : Nat) :
    ⦃fun state => ⌜state.x = a ∧ state.y = b⌝⦄swap⦃⇓ _ state => ⌜state.x = b ∧ state.y = a⌝⦄ := by
  mvcgen [swap]
  grind

def swap_swap : StateM TwoVals Unit := do
  swap; swap

theorem swap_swap_spec (s : TwoVals) :
    (swap_swap.run s).snd = s := by
  generalize h : swap.run s = x
  apply StateM.of_wp_run_eq h
  mvcgen

namespace hidden

structure Supply where
  counter : Nat
  limit : Nat
  property : counter ≤ limit

def mkFresh : EStateM String Supply Nat := do
  let supply ← get
  if h : supply.counter = supply.limit then
    throw s!"Supply exhausted: {supply.counter} = {supply.limit}"
  else
    let n := supply.counter
    have := supply.property
    set { supply with counter := n + 1, property := by grind }
    pure n

@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃post⟨fun r state => ⌜r = c ∧ c < state.counter⌝,
          fun _ state => ⌜c = state.counter ∧ c = state.limit⌝⟩⦄ := by
  mvcgen [mkFresh] with grind

end hidden
