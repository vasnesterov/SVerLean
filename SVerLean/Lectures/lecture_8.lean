import SVerLean.Lectures.lecture_7

set_option linter.hashCommand false
set_option linter.style.commandStart false

-- Чтобы `grind` всегда по умолчанию раскрывал `Function.update`
attribute [grind] Function.update

/- # Тройки Хоара

Тройки Хоара - это удобный язык для спецификации программ.
Де-факто, тройки Хоара являются стандартом в верификации программ, потому что они позволяют
доказывать необходимые свойства программ автоматически.

Тройки Хоара имеют вид `{P}S{Q}`, где `P` и `Q` - предикаты на состояниях,
а `S` - программа. `P` называется предусловием (precondition),
а `Q` - постусловием (postcondition).

Тройка Хоара `{P}S{Q}` означает что если до выполнения `S` было верно `P`, и программа
`S` завершится, то после выполнения `S` будет верно `Q`.

Примеры:
  `{x = 10}(x := x * 2){x = 20}` - верное утверждение.

  `{True}(while x > 0 do x := x - 1){x = 0}` - верное утверждение.

  `{False}S{P}` - верное утверждение для любой программы `S` и условия `P`, потому что
    предусловие всегда ложно.

  `{True}(while true do skip){False}` - верное утверждение, потому что программа никогда не
  завершится.

  `{True}(while i ≠ 10 do i := i + 1){i = 10}` - верное утверждение (почему?)

Для троек Хоара можно сделать исчисление, подобно big-step-семантике и small-step-семантике:


——————————————— Skip
  {P} skip {P}


————————————————————— Assign
 {Q[a/x]} x := a {Q}

(Q[a/x] - это предикат, полученный из `Q` заменой всех вхождений `x` на `a`)


{P} S {R}      {R} T {Q}
———————————————————————— Seq
      {P} S;T {Q}


{P ∧ B} S {Q}      {P ∧ ¬ B} T {Q}
—————————————————————————————————— If
    {P} if B then S else T {Q}


        {P ∧ B} S {P}
——————————————————————————————— While
  {P} while B do S {P ∧ ¬ B}


P' → P     {P}  S {Q}      Q → Q'
———————————————————————————————— Conseq
           {P'} S {Q'}

Правило Assign может выглядеть контринтуитивно, потому что в нем предусловие зависит от
постусловия. На самом деле оно верно отображает смысл присваивания. Примеры:
  `{0 = 0} x := 0 {x = 0}`

  `{0 = 0 ∧ y = 5} x := 0 {x = 0 ∧ y = 5}`

  `{x + 1 ≥ 5} x := x + 1 {x ≥ 5}`
-/

/--
В Lean мы могли бы определить тройки Хоара через это исчисление при помощи индуктивного
предиката, как мы сделали для операционной семантики. И потом доказать что тройки Хоара
выражаются через big-step-семантику. Можно сделать наоборот: определим тройки Хоара через
big-step-семантику и затем докажем правила вывода как теоремы.
-/
@[irreducible]
def PartialHoare (P : State → Prop) (S : Stmt)
  (Q : State → Prop) : Prop :=
  ∀ s t, P s → (S, s) ⟹ t → Q t
-- (слово Partial означает что мы не требуем чтобы программа завершалась)

-- введем нотацию для троек Хоара
notation3:101 "{" P:100 "}" S:100 "{" Q:100 "}" => PartialHoare P S Q

#check {fun _ ↦ True}Stmt.skip{fun _ ↦ True}



namespace PartialHoare
-- докажем правила вывода

theorem skip_intro {P} : { P }Stmt.skip{ P } := by
  unfold PartialHoare
  intro s t h hstep
  cases hstep
  exact h

theorem assign_intro (P) {x a} :
    {fun s ↦ P (Function.update s x (a s))}(Stmt.assign x a){ P } := by
  unfold PartialHoare
  intro s t h hstep
  cases hstep
  exact h

theorem seq_intro {P Q R S T}
    (hS : { P }S{ Q }) (hT : { Q }T{ R }) :
    { P }(S; T){ R } := by
  unfold PartialHoare at *
  intro s t h hstep
  cases hstep with
  | seq _ _ _ u _ hSU hTu =>
  apply hT
  · apply hS
    · exact h
    · exact hSU
  · exact hTu

theorem if_intro {B P Q S T}
    (hS : {fun s ↦ P s ∧ B s }S{ Q }) (hT : {fun s ↦ P s ∧ ¬ B s }T{ Q }) :
    { P }(.ifThenElse B S T){ Q } := by
  unfold PartialHoare at *
  intro s t h hstep
  cases hstep with
  | ifTrue B S T s t hcond hS' =>
    apply hS
    · exact ⟨h, hcond⟩
    · exact hS'
  | ifFalse B S T s t hcond hT' =>
    apply hT
    · exact ⟨h, hcond⟩
    · exact hT'

theorem while_intro (P) {B S}
    (hS : { fun s ↦ P s ∧ B s }S{ P }) :
    { P }(.whileDo B S){ fun s ↦ P s ∧ ¬ B s } := by
  unfold PartialHoare at *
  intro s t h hstep
  generalize hC : (Stmt.whileDo B S, s) = C at hstep
  induction hstep generalizing S s <;> try grind
  case whileTrue B' S' s' t' u hcond hbody hrest hbody_ih hrest_ih =>
  injection hC with h1 h2
  injection h1 with h3 h4
  subst h2 h3 h4
  apply hrest_ih
  · exact hS
  swap
  · rfl
  apply hS
  swap
  · exact hbody
  exact ⟨h, hcond⟩

theorem consequence {P P' Q Q' S}
    (h : { P }S{ Q }) (hp : ∀s, P' s → P s)
    (hq : ∀s, Q s → Q' s) :
    { P' }S{ Q' } := by
  grind [PartialHoare]

/-
Наша цель: сделать так чтобы доказательство `{P}S{Q}` происходило
в (полу)автоматическом режиме. Первое что нам для этого понадобится -
вспомогательные правила, утверждения которых матчатся с тройками вида `{P}S{Q}`,
где `S` - некоторый конструктор `Stmt`, а `P` и `Q` - **произвольные** предикаты.
Тогда в любой ситуации, когда нам нужно доказать `{P}S{Q}`,
мы можем использовать `apply` с одним из таких правил.
-/

/-- Упрощение `consequence` в котором изменяется только предусловие. -/
theorem consequence_left {P' P Q S}
    (h : { P }S{ Q }) (hp : ∀ s, P' s → P s) :
    { P' }S{ Q } := by
  apply consequence
  · exact h
  · grind
  · grind

/-- Упрощение `consequence` в котором изменяется только постусловие. -/
theorem consequence_right {Q Q' P S}
    (h : { P }S{ Q }) (hq : ∀ s, Q s → Q' s) :
    { P }S{ Q' } := by
  apply consequence
  · exact h
  · grind
  · grind

/-- Правило для `skip` которое работает для любого `P` и `Q`. -/
theorem skip_intro' {P Q} (h : ∀ s, P s → Q s) :
    { P }(Stmt.skip){ Q } := by
  apply consequence_right
  · exact skip_intro
  · exact h

/-- Правило для `assign` которое работает для любого `P` и `Q`. -/
theorem assign_intro' {P Q x a}
    (h : ∀ s, P s → Q (Function.update s x (a s))) :
    { P }(Stmt.assign x a){ Q } := by
  apply consequence_left
  · apply assign_intro
  · exact h

/-- Правило для `seq` которое отличается от обычного только порядком аргументов.
Оно нужно потому что `A; B; C` парсится как `(A; B); C` а не как `A; (B; C)`.
Поэтому если текущая цель имеет вид `{P}(A; B; C){Q}` после применения правила
для `seq` у нас будут две цели: `{P}(A; B){?R}` и `{?R}C{Q}`,
где `?R` - метапеременная. Если мы первым делом займемся второй целью, мы сможем
автоматически понять чему равно `?R`, потому что в наших правилах предусловия
вычисляются из постусловий. -/
theorem seq_intro' {P Q R S T}
    (hT : { Q }T{ R }) (hS : { P }S{ Q }) :
    { P }(S; T){ R } := by
  exact seq_intro hS hT

/-- Правило для `while` которое работает для любого `P` и `Q`. -/
theorem while_intro' {B P Q S} (I : State → Prop)
    (hS : {fun s => I s ∧ B s }S{ I })
    (hP : ∀ s, P s → I s)
    (hQ : ∀ s, ¬ B s → I s → Q s) :
    { P }(Stmt.whileDo B S){ Q } := by
  apply consequence_left _ hP
  apply consequence_right
  · apply while_intro
    exact hS
  tauto

end PartialHoare

/- Опробуем наши правила на конкретных программах. -/

open PartialHoare

def swap : Stmt :=
  .assign "t" (fun s ↦ s "a");
  .assign "a" (fun s ↦ s "b");
  .assign "b" (fun s ↦ s "t")

theorem swap_correct (x y : ℕ) :
    {fun s ↦ s "a" = x ∧ s "b" = y }swap{ fun s ↦ s "a" = y ∧ s "b" = x } := by
  unfold swap
  apply seq_intro'
  · apply assign_intro -- автоматически заполняет метапеременную `?Q`
  apply seq_intro'
  · apply assign_intro
  apply assign_intro'
  -- цель выглядит страшно, но `grind` разберется
  grind


def add : Stmt :=
  .whileDo (fun s ↦ s "n" ≠ 0) (
    .assign "n" (fun s ↦ s "n" - 1);
    .assign "m" (fun s ↦ s "m" + 1)
  )

theorem add_correct (x y : ℕ) :
    {fun s ↦ s "n" = x ∧ s "m" = y }add{ fun s ↦ s "n" = 0 ∧ s "m" = x + y } := by
  unfold add
  -- Здесь нужно придумать инвариант `I` для цикла
  -- Он должен удовлетворять 3 условиям
  -- 1. Он верен до начала цикла
  -- 2. Если он верен в начале итерации, то он верен и после ее завершения
  -- 3. Из него должно следовать постусловие в момент завершения цикла
  -- `I = True` удовлетворяет условиям 1 и 2, но не 3
  -- `I = False` удовлетворяет 2 и 3, но не 1
  -- Обычно выбирают по схеме `I := "что сделано + что осталось сделать = цель"`.
  -- В начале цикла `сделано = 0` и `I` эквивалентен `осталось сделать = цель`
  -- На каждой итерации `сделано` увеличивается, `осталось сделать` уменьшается,
  --   и они продолжают "суммироваться" в `цель`
  -- В конце цикла `сделано = цель`
  --
  -- В нашем случае давайте возьмем `сделано := m` (`m` накапливает сумму),
  -- и `осталось сделать := n` (`n` показывает сколько раз еще нужно переложить единицу
  --   из `n` в `m`)
  -- `цель := x + y`
  apply while_intro' (fun (s : State) ↦ s "n" + s "m" = x + y)
  -- в теле цикла
  · apply seq_intro'
    · apply assign_intro
    apply assign_intro'
    grind
  -- перед началом цикла
  · grind
  -- в конце цикла
  · grind

/-
Пойдем дальше в автоматизации. Пусть `apply` (единственного) подходящего правила
за нас будет делать специальная тактика, а нам оставлять только логические доп.
условия правил (как например инвариантность `I` в `while_intro'`).
Такие программы/тактики называются verification condition generators (VCG).

Единственная проблема: по коду программы непонятно как выбирать инварианты для циклов.
Решение: мы *аннотируем* каждый цикл инвариантом.
-/

/-- Вместо `whileDo B S` мы будем писать `annWhileDo I B S` где `I` - инвариант.
`I` никак не влияет на работу программы, он нужен только чтобы помочь VCG. -/
def Stmt.annWhileDo (I : State → Prop) (B : State → Bool)
    (S : Stmt) : Stmt :=
  .whileDo B S

/- Докажем для `annWhileDo` те же правила что и для `whileDo`. -/

theorem PartialHoare.annWhile_intro {B I Q S}
    (hS : {fun s ↦ I s ∧ B s }S{ I })
    (hQ : ∀ s, ¬ B s → I s → Q s) :
    { I }(.annWhileDo I B S){ Q } :=
  while_intro' I hS (by grind) hQ

theorem PartialHoare.annWhile_intro' {B I P Q S}
    (hS : {fun s ↦ I s ∧ B s }S{ I })
    (hP : ∀s, P s → I s) (hQ : ∀s, ¬ B s → I s → Q s) :
    { P }(.annWhileDo I B S){ Q } :=
  while_intro' I hS hP hQ

/- Теперь напишем VCG в виде простой тактики. -/

section metaprogramming

open Lean Meta Elab Tactic

/-- Парсит `{P}S{Q}` на `P`, `S` и `Q`. -/
def matchPartialHoare : Expr → Option (Expr × Expr × Expr)
| (Expr.app (Expr.app (Expr.app (Expr.const ``PartialHoare _) P) S) Q) =>
  some (P, S, Q)
| _ => none

/-- Делает `apply name` в текущей цели. -/
def applyConstant (name : Name) : TacticM Unit := do
  let cst ← mkConstWithFreshMVarLevels name
  liftMetaTactic (fun goal ↦ MVarId.apply goal cst)

/-- Сама тактика VCG. На текущей цели `{P}S{Q}` она пытается применить
подходящее правило, и рекурсивно применяется к подцелям, которые тоже
имеют вид `{P}S{Q}`. Остальные подцели остаются нам. -/
partial def vcg : TacticM Unit := do
  let goals ← getUnsolvedGoals
  if goals.length ≠ 0 then
  let target ← getMainTarget
  match_expr target with
  | PartialHoare P S Q =>
    match_expr S with
    | Stmt.skip =>
      if Expr.isMVar P then
        applyConstant ``PartialHoare.skip_intro
      else
        applyConstant ``PartialHoare.skip_intro'
    | Stmt.assign x a =>
      if Expr.isMVar P then
        applyConstant ``PartialHoare.assign_intro
      else
        applyConstant ``PartialHoare.assign_intro'
    | Stmt.seq S T =>
      andThenOnSubgoals
        (applyConstant ``PartialHoare.seq_intro') vcg
    | Stmt.ifThenElse B S T =>
      andThenOnSubgoals
        (applyConstant ``PartialHoare.if_intro) vcg
    | Stmt.annWhileDo I B S =>
      if Expr.isMVar P then
        andThenOnSubgoals
          (applyConstant ``PartialHoare.annWhile_intro) vcg
      else
        andThenOnSubgoals
          (applyConstant ``PartialHoare.annWhile_intro') vcg
    | _ =>
      dbg_trace f!"Unknown statement {← ppExpr S}"
      failure
  | _ => return

elab "vcg" : tactic => vcg

end metaprogramming

theorem add_correct_vcg (x y : ℕ) :
    {fun s ↦ s "n" = x ∧ s "m" = y }add{ fun s ↦ s "n" = 0 ∧ s "m" = x + y } := by
  -- аннотируем нашу программу
  let add' : Stmt :=
    .annWhileDo (fun s ↦ s "n" + s "m" = x + y) (fun s ↦ s "n" ≠ 0) (
      .assign "n" (fun s ↦ s "n" - 1);
      .assign "m" (fun s ↦ s "m" + 1)
    )
  -- `change` заменит `add` на `add'` потому что `add'`
  -- по определению равен `add` (ведь аннотации никак не используются)
  change { _ }add'{ _ }
  unfold add'
  -- теперь мы можем использовать `vcg`
  vcg
  -- `grind` закроет все цели
  all_goals grind

/-
Описанное выше - самый популярный подход к верификации программ.
Мы пишем код, аннотируем его, дальше VCG раскручивает логику Хоара, а
мощная тактика (`grind`, или, обычно, какой-нибудь SMT solver) доказывает все
промежуточные условия.

В такой парадигме программисту вообще не требуется ничего доказывать самому,
единственное что нужно сделать - грамотно все аннотировать.
-/






/- # Логика Хоара для тотальной корректности

До этого момента мы рассматривали тройки `{P}S{Q}` которые всегда верны, если
`S` не завершается. Работать с ними проще, но они не гарантируют завершение
программы. Чтобы это исправить рассмотрим тройки вида `[P]S[Q]`, которые верны
если для любого состояния `s` такого что `P s` программа `S` завершается в
состоянии `t`, удовлетворяющем `Q`.

Для таких троек мы можем использовать исчисление, подобное рассмотренному выше.
Отличие будет только в правиле для циклов:

[P ∧ B ∧ v = v₀] S [P ∧ v < v₀]
——————————————————————————————— While
  [P] while B do S [P ∧ ¬ B]

`v` - это некоторая функция `State → ℕ` которая на каждой итерации цикла
уменьшается, тем самым гарантируя его завершение.
-/


@[irreducible]
def StrictHoare (P : State → Prop) (S : Stmt) (Q : State → Prop) : Prop :=
  ∀ s, P s → ∃ t, (S, s) ⟹ t ∧ Q t

notation3:101 "[*" P:100 "*]" S:100 "[*" Q:100 "*]" => StrictHoare P S Q

#check [* fun s ↦ True *]Stmt.skip[* fun s ↦ True *]

namespace StrictHoare

theorem skip_intro {P} : [* P *]Stmt.skip[* P *] := by
  unfold StrictHoare
  intro s hP
  use s
  constructor
  · exact BigStep.skip s
  · exact hP

theorem assign_intro (P) {x a} :
    [* fun s ↦ P (Function.update s x (a s)) *](Stmt.assign x a)[* P *] := by
  unfold StrictHoare
  intro s h
  use Function.update s x (a s)
  constructor
  · exact BigStep.assign x a s
  · exact h

theorem seq_intro {P Q R S T}
    (hS : [* P *]S[* Q *]) (hT : [* Q *]T[* R *]) :
    [* P *](S; T)[* R *] := by
  unfold StrictHoare at *
  intro s hP
  obtain ⟨t, hSt, hQ⟩ := hS s hP
  obtain ⟨u, hTu, hR⟩ := hT t hQ
  use u
  constructor
  · constructor
    · exact hSt
    · exact hTu
  · exact hR

theorem if_intro {B P Q S T}
    (hS : [* fun s ↦ P s ∧ B s *]S[* Q *]) (hT : [* fun s ↦ P s ∧ ¬ B s *]T[* Q *]) :
    [* P *](.ifThenElse B S T)[* Q *] := by
  unfold StrictHoare at *
  intro s hP
  by_cases hB : B s
  · obtain ⟨t, hSt, hQ⟩ := hS s ⟨hP, hB⟩
    use t
    constructor
    · apply BigStep.ifTrue
      · exact hB
      · exact hSt
    · exact hQ
  · obtain ⟨t, hSt, hQ⟩ := hT s ⟨hP, hB⟩
    use t
    constructor
    · apply BigStep.ifFalse
      · exact hB
      · exact hSt
    · exact hQ

theorem while_intro {B P S} (v : State → ℕ)
    (hS : ∀ v₀, [* fun s ↦ P s ∧ B s ∧ v s = v₀ *]S[* fun s ↦ P s ∧ v s < v₀ *]) :
    [* P *](.whileDo B S)[* fun s ↦ P s ∧ ¬ B s *] := by
  sorry

theorem consequence {P P' Q Q' S}
    (h : [* P *]S[* Q *]) (hp : ∀s, P' s → P s)
    (hq : ∀s, Q s → Q' s) :
    [* P' *]S[* Q' *] := by
  unfold StrictHoare at *
  intro s hP'
  obtain ⟨t, hSt, hQ⟩ := h s (hp s hP')
  use t
  constructor
  · exact hSt
  · exact hq t hQ

theorem consequence_left {P' P Q S}
    (h : [* P *]S[* Q *]) (hp : ∀ s, P' s → P s) :
    [* P' *]S[* Q *] := by
  apply consequence
  · exact h
  · exact hp
  · grind

theorem consequence_right {Q Q' P S}
    (h : [* P *]S[* Q *]) (hq : ∀ s, Q s → Q' s) :
    [* P *]S[* Q' *] := by
  apply consequence
  · exact h
  · grind
  · exact hq

theorem skip_intro' {P Q} (h : ∀ s, P s → Q s) :
    [* P *]Stmt.skip[* Q *] := by
  apply consequence_right
  · exact skip_intro
  · exact h

theorem assign_intro' {P Q x a}
    (h : ∀ s, P s → Q (Function.update s x (a s))) :
    [* P *](Stmt.assign x a)[* Q *] := by
  apply consequence_left
  · apply assign_intro
  · exact h

theorem seq_intro' {P Q R S T}
    (hT : [* Q *]T[* R *]) (hS : [* P *]S[* Q *]) :
    [* P *](S; T)[* R *] := by
  exact seq_intro hS hT

theorem while_intro' {B P Q S} (I : State → Prop) (v : State → ℕ)
    (hS : ∀ v₀, [* fun s ↦ I s ∧ B s ∧ v s = v₀ *]S[* fun s ↦ I s ∧ v s < v₀ *])
    (hPI : ∀ s, P s → I s)
    (hIQ : ∀ s, ¬ B s → I s → Q s) :
    [* P *](.whileDo B S)[* Q *] := by
  apply consequence (while_intro v hS)
  · exact hPI
  · intro s ⟨hI, hnotB⟩
    exact hIQ s hnotB hI

def _root_.Stmt.tannWhileDo (I : State → Prop) (v : State → ℕ) (B : State → Bool) (S : Stmt) : Stmt :=
  .whileDo B S

theorem tannWhile_intro {B I Q S v}
    (hS : ∀ v₀, [* fun s ↦ I s ∧ B s ∧ v s = v₀ *]S[* fun s ↦ I s ∧ v s < v₀ *])
    (hQ : ∀ s, ¬ B s → I s → Q s) :
    [* I *](Stmt.tannWhileDo I v B S)[* Q *] :=
  while_intro' I v hS (by grind) hQ

theorem tannWhile_intro' {B I P Q S v}
    (hS : ∀ v₀, [* fun s ↦ I s ∧ B s ∧ v s = v₀ *]S[* fun s ↦ I s ∧ v s < v₀ *])
    (hP : ∀s, P s → I s) (hQ : ∀s, ¬ B s → I s → Q s) :
    [* P *](Stmt.tannWhileDo I v B S)[* Q *] :=
  while_intro' I v hS hP hQ

end StrictHoare

section metaprogramming

open Lean Meta Elab Tactic Qq

partial def totalVcg : TacticM Unit := do
  let goals ← getUnsolvedGoals
  if goals.length ≠ 0 then
  let target ← getMainTarget
  match_expr target with
  | StrictHoare P S Q =>
    match_expr S with
    | Stmt.skip =>
      if Expr.isMVar P then
        applyConstant ``StrictHoare.skip_intro
      else
        applyConstant ``StrictHoare.skip_intro'
    | Stmt.assign x a =>
      if Expr.isMVar P then
        applyConstant ``StrictHoare.assign_intro
      else
        applyConstant ``StrictHoare.assign_intro'
    | Stmt.seq S T =>
      andThenOnSubgoals
        (applyConstant ``StrictHoare.seq_intro') totalVcg
    | Stmt.ifThenElse B S T =>
      andThenOnSubgoals
        (applyConstant ``StrictHoare.if_intro) totalVcg
    | Stmt.tannWhileDo I v B S =>
      if Expr.isMVar P then
        let tac := evalTactic (← `(tactic| refine StrictHoare.tannWhile_intro (fun v₀ ↦ ?_) ?_))
        andThenOnSubgoals tac totalVcg
      else
        let tac := evalTactic (← `(tactic| refine StrictHoare.tannWhile_intro' (fun v₀ ↦ ?_) ?_ ?_))
        andThenOnSubgoals tac totalVcg
    | _ =>
      dbg_trace f!"Unknown statement {← ppExpr S}"
      failure
  | _ => return

elab "total_vcg" : tactic => totalVcg

end metaprogramming

theorem add_total_correct (x y : ℕ) :
    [* fun s ↦ s "n" = x ∧ s "m" = y *]add[* fun s ↦ s "n" = 0 ∧ s "m" = x + y *] := by
  let add' : Stmt :=
    .tannWhileDo
    (fun s ↦ s "n" + s "m" = x + y)
    (fun s ↦ s "n")
    (fun s ↦ s "n" ≠ 0) (
      .assign "n" (fun s ↦ s "n" - 1);
      .assign "m" (fun s ↦ s "m" + 1)
    )
  change [* _ *]add'[* _ *]
  unfold add'
  total_vcg <;> grind
