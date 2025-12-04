import SVerLean.Lectures.lecture_7

/- # Денотационная семантика

Мы рассматриваем третий способ задания семантики языка программирования:
денотационную семантику. Денотационная семантика пытается напрямую задать
значение программ.

Если операционная семантика — это идеализированный интерпретатор, а логика Хоара —
идеализированный верификатор, то денотационная семантика — это идеализированный
компилятор. -/


/- ## Композиционность

__Денотационная семантика__ определяет значение каждой программы как
математический объект:

    `⟦ ⟧ : syntax → semantics`

Ключевое свойство денотационной семантики — это __композиционность__: значение
составного оператора должно определяться через значения его компонентов.
То есть мы хотим нечто похожее на

  `⟦S⟧ = {(s, t) | (S, s) ⟹ t}` (как `Set (State × State)`),

но выраженное так чтобы

    `⟦S; T⟧               = … ⟦S⟧ … ⟦T⟧ …`
    `⟦if B then S else T⟧ = … ⟦S⟧ … ⟦T⟧ …`
    `⟦while B do S⟧       = … ⟦S⟧ …`

Например функция вычисления арифметических выражений

    `eval : ArithExpr → ((String → ℤ) → ℤ)`

является денотационной семантикой. Мы хотим то же самое для императивных программ.


## Реляционная денотационная семантика

Мы можем представить семантику императивной программы как функцию от начального
состояния к конечному состоянию или, более общо, как отношение между начальным
и конечным состояниями: `Set (State × State)`.
(См. файл `sets.lean` для ликбеза по тому как устроены множества в Lean)

Для `skip`, `:=`, `;` и `if then else` денотационная семантика проста: -/

open SetRel

-- SetRel α β := α → β → Prop

/-- Вспомогательная операция для `if-then-else` (см. ниже) -/
def SetRel.restrict {α β : Type*} (A : SetRel α β) (P : α → Bool) : SetRel α β :=
  A ∩ {p | P p.fst}

infixr:100 " ⇃ " => SetRel.restrict

namespace SorryDefs

def denote (S : Stmt) : SetRel State State :=
  match S with
  | .skip             => SetRel.id -- диагональ, то есть множество пар вида `(s, s)`
  | .assign x a       => {(p, q) | q = Function.update p x (a p)}
  | .seq S T          => denote S ○ denote T -- композиция отношений
  | .ifThenElse B S T => (denote S ⇃ B) ∪ (denote T ⇃ (fun p ↦ ¬ B p))
  | .whileDo B S      => sorry -- как быть здесь?

end SorryDefs

/- Мы пишем `⟦S⟧` для `denote S`. Для `while` мы хотели бы написать
  `⟦while B do S⟧ = (⟦S⟧ ○ ⟦while B do S⟧) ⇃ B ∪ id ⇃ (¬ B)`

но это некорректно из-за рекурсивного вызова на `whileDo B S`.

Мы ищем такое `X`, что

    `X = ((denote S ○ X) ⇃ B) ∪ (Id ⇃ (fun s ↦ ¬ B s))`

Другими словами, мы ищем *неподвижную точку* некоторого отображения `F(X)`.

Большая часть этой лекции посвящена построению оператора наименьшей неподвижной
точки `lfp` (least fixed point), который позволит нам определить семантику `while`:

## Неподвижные точки

__Неподвижная точка__ (fixed point) функции `F` — это решение для `X`
в уравнении

    `X = F X`

В общем случае неподвижные точки могут вообще не существовать (например, `f := Nat.succ`),
или их может быть несколько (например, `f = id`). Но при некоторых условиях на `f`
гарантируется существование единственной __наименьшей неподвижной точки__ и единственной
__наибольшей неподвижной точки__.

Например рассмотрим следующее уравнение:

    `X = (fun (P : ℕ → Prop) (n : ℕ) ↦ n = 0 ∨ ∃ m : ℕ, n = m + 2 ∧ P m) X`
      `= (fun n : ℕ ↦ n = 0 ∨ ∃ m : ℕ, n = m + 2 ∧ X m)`

где `X : ℕ → Prop` и
`f := (fun (P : ℕ → Prop) (n : ℕ) ↦ n = 0 ∨ ∃ m : ℕ, n = m + 2 ∧ P m)`.

Приведённый пример допускает только одну неподвижную точку. Уравнение неподвижной точки
однозначно задаёт `X` как предикат, определяющий чётные числа.

В общем случае наименьшая и наибольшая неподвижные точки могут различаться. Например для
`F : Set α → Set α := fun X ↦ X`
наименьшая неподвижная точка это `∅`, наибольшая -- `Set.univ`.

Для семантики языков программирования:

* `X` будет иметь тип `SetRel State State` (который изоморфен
  `State → State → Prop`), представляя отношения между состояниями;

* `F` будет соответствовать либо выполнению одной дополнительной итерации цикла (если
  условие `B` истинно), либо тождеству (если `B` ложно).

Тогда мы положим `⟦while B do S⟧ := lfp F` (lpf = least fixed point, наименьшая неподвижная точка).
Почему именно наименьшая? Поговорим чуть позже. Сейчас докажем что lfp действительно существует.


## 1. Монотонные функции

Пусть `α` и `β` — типы с частичным порядком `≤`. Функция `f : α → β` называется
__монотонной__, если

    `a₁ ≤ a₂ → f a₁ ≤ f a₂`   для всех `a₁`, `a₂`

Многие операции над множествами (например, `∪`), отношениями (например, `○`) и функциями
(например, `fun x ↦ x`, `fun _ ↦ const`, `∘`) являются монотонными или сохраняют монотонность.

Все монотонные функции `f : Set α → Set α` допускают наименьшие и наибольшие
неподвижные точки. На самом деле это верно если мы заменим `Set α` на любую полную решётку.

## Полные решётки

Полная решётка (complete lattice) - это алгебраическая структура со следующими свойствами:

1. На ней есть частичный порядок `≤`
2. У любого подмножества `S` есть инфимум `⨅ S`,
  т.е. наименьший такой элемент `x` что `x ≤ a` для всех `a ∈ S`.
3. Аналогично у каждого подмножества `S` есть супремум `⨆ S`,
  т.е. наибольший такой элемент `x` что `a ≤ x` для всех `a ∈ S`.

Самый главный пример это `Set α` с порядком `⊆`, инфимумом `⋂` и супремумом `⋃`.
Более общий пример: если `α` это полная решетка, то `α → β` тоже является полной решеткой с
порядком `f ≤ g := ∀ a, f a ≤ g a`, инфимумом `⨅ F := fun a ↦ ⨅ {f a | f ∈ F}`.
(Он более общий в том смысле что `Set α = α → Prop`, а `Prop` это полная решетка из двух точек
`True` и `False` с порядком `False < True`.)

**Теорема Кнастера-Тарского:** Для любой монотонной функции `f` из полной решётки в себя существуют
наименьшая (`lfp`) и наибольшая (`gfp`) неподвижные точки, причем:

* `lfp f = ⨅ {X | f X ≤ X}`
* `gfp f = ⨆ {X | X ≤ f X}`

/- ## Реляционная денотационная семантика, продолжение -/

Теперь мы можем завершить определение `denote`:
-/

mutual

  def denote (S : Stmt) : SetRel State State :=
    match S with
    | Stmt.skip             => SetRel.id
    | Stmt.assign x a       =>
      {(p, q) | q = Function.update p x (a p)}
    | Stmt.seq S T          => denote S ○ denote T
    | Stmt.ifThenElse B S T => (denote S ⇃ B) ∪ (denote T ⇃ (fun p ↦ ¬ B p))
    | Stmt.whileDo B S      => (whileStep B S).lfp -- берем lfp

  /-- Монотонное отображение из решетки `SetRel State State` в себя.
  Здесь мы используем тип `OrderHom` из mathlib и нотацию `→o` для
  обозначения монотонных функций. -/
  def whileStep (B : State → Bool) (S : Stmt) : (SetRel State State) →o (SetRel State State) where
    toFun P := (denote S ○ P) ⇃ B ∪ SetRel.id ⇃ (fun s ↦ ¬ B s)
    monotone' := by
      -- "структурная" монотонность, ничего нетривиального
      -- по-хорошему должна быть тактика для таких целей
      apply Monotone.union
      · apply Monotone.inter
        · apply Monotone.relComp
          · apply monotone_const
          · apply monotone_id
        · apply monotone_const
      · apply Monotone.inter
        · apply monotone_const
        · apply monotone_const

end

notation (priority := high) "⟦" S "⟧" => denote S

@[simp]
theorem denote_skip : ⟦Stmt.skip⟧ = SetRel.id := by
  simp [denote]

@[simp]
theorem denote_assign (x a) : ⟦Stmt.assign x a⟧ = {(p, q) | q = Function.update p x (a p)} := by
  simp [denote]

@[simp]
theorem denote_seq (S T) : ⟦S; T⟧ = ⟦S⟧ ○ ⟦T⟧ := by
  simp [denote]

@[simp]
theorem denote_ifThenElse (B S T) :
    ⟦Stmt.ifThenElse B S T⟧ = (⟦S⟧ ⇃ B) ∪ (⟦T⟧ ⇃ (fun p ↦ ¬ B p)) := by
  simp [denote]

-- это нельзя сделать `simp`-леммой: будет бесконечный цикл
theorem denote_whileDo (B S) :
    ⟦Stmt.whileDo B S⟧ = ((⟦S⟧ ○ ⟦Stmt.whileDo B S⟧) ⇃ B) ∪ (SetRel.id ⇃ (fun p ↦ ¬ B p)) := by
  conv => lhs; simp [denote]; rw [← OrderHom.isFixedPt_lfp]
  simp only [denote]
  generalize (whileStep B S).lfp = X
  simp [whileStep]


/- ## Применение к эквивалентности программ

На основе денотационной семантики мы можем говорить об эквивалентности программ:
`S₁ ~ S₂`. -/

def DenoteEquiv (S₁ S₂ : Stmt) : Prop :=
  ⟦S₁⟧ = ⟦S₂⟧

instance : Setoid (Stmt)  where
  r := DenoteEquiv
  iseqv := by
    constructor
    · grind [DenoteEquiv]
    · grind [DenoteEquiv]
    · grind [DenoteEquiv]

infix:50 (priority := high) " ~ " => DenoteEquiv

/- Из определения очевидно, что `~` является отношением эквивалентности.

Эквивалентность программ может использоваться для замены подпрограмм другими
подпрограммами с той же семантикой. Это достигается следующими правилами конгруэнтности: -/

lemma DenoteEquiv.whileStep_congr {B S₁ S₂}
      (hS : S₁ ~ S₂) :
    whileStep B S₁ = whileStep B S₂ := by
  simp [DenoteEquiv, whileStep] at *
  rw [hS]

theorem DenoteEquiv.seq_congr {S₁ S₂ T₁ T₂ : Stmt}
      (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    S₁; T₁ ~ S₂; T₂ := by
  simp [DenoteEquiv] at *
  rw [hS, hT]

theorem DenoteEquiv.if_congr {B} {S₁ S₂ T₁ T₂ : Stmt}
      (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ := by
  simp [DenoteEquiv] at *
  simp [*]

theorem DenoteEquiv.while_congr {B} {S₁ S₂ : Stmt}
      (hS : S₁ ~ S₂) :
    Stmt.whileDo B S₁ ~ Stmt.whileDo B S₂ := by
  simp [DenoteEquiv, denote] at *
  rw [whileStep_congr]
  exact hS

/- Доказательства получаются такими простыми благодаря композиционности денотационной семантики.

Давайте докажем некоторые эквивалентности программ. -/

theorem DenoteEquiv.skip_assign_id {x} :
    Stmt.assign x (fun s ↦ s x) ~ Stmt.skip := by
  simp [DenoteEquiv, SetRel.id]
  grind

theorem DenoteEquiv.seq_skip_left {S} :
    Stmt.skip; S ~ S := by
  simp [DenoteEquiv, SetRel.comp]

theorem DenoteEquiv.seq_skip_right {S} :
    S; Stmt.skip ~ S := by
  simp [DenoteEquiv, SetRel.comp]

theorem DenoteEquiv.if_seq_while {B S} :
    Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip
    ~ Stmt.whileDo B S := by
  simp [DenoteEquiv]
  conv => rhs; rw [denote_whileDo]
  simp

/- ## Эквивалентность денотационной семантики и Big-step семантики

Big-step семантика и рассмотренная выше денотационная семантика
выражаются друг через друга.
-/

theorem denote_of_BigStep (Ss : Stmt × State) (t : State)
      (h : Ss ⟹ t) :
    (Prod.snd Ss, t) ∈ ⟦Prod.fst Ss⟧ := by
  induction h with
  | skip s => simp
  | assign x a s => simp
  | seq S T s t u hS hT ihS ihT => aesop
  | ifTrue B S T s t hB hS ih => simp_all [SetRel.restrict]
  | ifFalse B S T s t hB hT ih => simp_all [SetRel.restrict]
  | whileTrue B S s t u hB hS hw ihS ihw =>
    simp at ihS ihw ⊢
    rw [denote_whileDo]
    left
    simp [SetRel.restrict]
    grind
  | whileFalse B S s hB =>
    rw [denote_whileDo]
    simp_all [SetRel.id, SetRel.restrict]

theorem BigStep_of_denote (S : Stmt) (s t : State) (h : (s, t) ∈ ⟦S⟧) :
    (S, s) ⟹ t := by
  induction S generalizing s t with
  | skip => simpa using h
  | assign x a => simpa using h
  | seq S T ihS ihT =>
    simp at h
    obtain ⟨u, hsu, hut⟩ := h
    simp
    use u
    grind
  | ifThenElse B S T ihS ihT =>
    simp [SetRel.restrict] at h
    obtain ⟨hst, hB⟩ | ⟨hst, hB⟩ := h
    · apply BigStep.ifTrue <;> grind
    · apply BigStep.ifFalse <;> grind
  | whileDo B S ihS =>
    let X (B : State → Bool) (S : Stmt) : SetRel State State :=
      {(s, t) | (Stmt.whileDo B S, s) ⟹ t}
    change (s, t) ∈ X B S
    suffices whileStep B S (X B S) ⊆ X B S by
      have := OrderHom.lfp_le _ this -- здесь мы впервые используем то что наша неподвижная точка
                                     -- наименьшая
      apply this
      simp [denote] at h
      exact h
    intro (s, t) h
    simp [whileStep, X, SetRel.restrict] at h ⊢
    obtain ⟨⟨u, hsu, hut⟩, hB⟩ | ⟨hst, hB⟩ := h
    · apply BigStep.whileTrue
      · exact hB
      · apply ihS
        exact hsu
      · exact hut
    · simp [hst]
      apply BigStep.whileFalse
      grind

theorem denote_Iff_BigStep (S : Stmt) (s t : State) :
    (s, t) ∈ ⟦S⟧ ↔ (S, s) ⟹ t :=
  Iff.intro (BigStep_of_denote S s t) (denote_of_BigStep (S, s) t)


/- ## Можно обойтись без lfp, если использовать индуктивные предикаты

На самом деле в данном случае можно было бы не возиться с lfp, и использовать индуктивный
предикат. Дело в том что индуктивные типы и предикаты это в точности неподвижные точки
некоторых монотонных отображений (каких?). -/

inductive Awhile (B : State → Bool) (X : SetRel State State) :
    SetRel State State -- State × State → Prop
  | loop {s t u} (hcond : B s) (hbody : (s, t) ∈ X)
      (hrest : Awhile B X (t, u)) :
    Awhile B X (s, u)
  | exit {s} (hcond : ¬ B s) :
    Awhile B X (s, s)

def denote' (S : Stmt) : SetRel State State :=
  match S with
  | Stmt.skip             => SetRel.id
  | Stmt.assign x a       =>
    {(p, q) | q = Function.update p x (a p)}
  | Stmt.seq S T          => denote S ○ denote T
  | Stmt.ifThenElse B S T => (denote S ⇃ B) ∪ (denote T ⇃ (fun p ↦ ¬ B p))
  | Stmt.whileDo B S      => Awhile B (denote S)
