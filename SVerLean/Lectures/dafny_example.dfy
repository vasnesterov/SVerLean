// Dafny это язык программирования в котором можно аннотировать программы
// в стиле Хоара и проверять корректность автоматически
// при помощи SMT-солвера
// Этот файл служит примером для лекции lecture_8.lean

// объявление метода (метод в Dafny ≈ функция в других ЯП)
method Abs(x: int) returns (y: int)
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}

// методы можно аннотировать
method Abs1(x: int) returns (y: int)
  ensures 0 <= y // постусловие
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}

// ensures может быть много
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures less < x
  ensures x < more
{
  more := x + y;
  less := x - y;
}

method MultipleReturns1(x: int, y: int) returns (more: int, less: int)
  ensures less < x < more // краткая запись предыдущего
{
  more := x + y;
  less := x - y;
}
// но возникает ошибка из-за того что Dafny не может доказать
// верность постусловия

// чтобы постусловие стало верным нужно добавить предусловие
method MultipleReturns2(x: int, y: int) returns (more: int, less: int)
  requires 0 < y
  ensures less < x < more
{
  more := x + y;
  less := x - y;
}

method Abs3(x: int) returns (y: int)
  ensures 0 <= y
{
  y := 0;
}
method Testing()
{
  var v := Abs3(3);
  assert 0 <= v; // чтобы проверить может ли Dafny доказать
                 // какой-то факт, можно написать assert
  assert v == 3; // не проходит потому что не следует из
                 // спецификации Abs3
}

// вот так сработает:
method Abs5(x: int) returns (y: int)
  ensures 0 <= y
  ensures 0 <= x ==> y == x
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}
method Testing5()
{
  var v := Abs5(3);
  assert 0 <= v;
  assert v == 3;
}

// Циклы:
method m(n: nat)
{
  var i := 0;
  while i < n
  {
    i := i + 1;
  }
  assert i == n; // Как убедить Dafny что это верно?
}

// Нужно аннотировать цикл инвариантом
method m2(n: nat)
{
  var i := 0;
  while i < n
    invariant 0 <= i // какой здесь подойдет инвариант?
  {
    i := i + 1;
  }
  assert i == n;
}

// Функции в Dafny отличаются от методов тем что они должны быть
// простыми, т.е. содержать только 1 выражение.
// Зато их можно использовать в выражениях (например, постусловиях)
// И Dafny при рассуждениях использует тело функции а не её спецификацию 
function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}
// Хотим написать быстрое вычисление fib
method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n) // и доказать что оно совпадает с fib
{
  var i := 1;
  var a := 0;
  b := 1;
  while i < n
    invariant 0 < i <= n // почему не проходит?
    invariant a == fib(i - 1)
    invariant b == fib(i)
  {
    a, b := b, a + b;
    i := i + 1;
  }
}

// Доказательства завершения (termination)
method m3 ()
{
  var i := 20;
  while 0 < i
    invariant 0 <= i
    decreases i // чтобы доказать что цикл завершается нужно указать 
                // убывающую меру. Часто Dafny может её угадать сама
  {
    i := i - 1;
  }
}

method m4()
{
  var i, n := 0, 20;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    i := i + 1;
  }
}

method NestedCountdown(a: nat, b: nat)
{
  var x := a;
  var y := b;

  while x > 0 || y > 0
    invariant 0 <= x <= a
    invariant 0 <= y <= b
    decreases x // какая здесь убывающая мера?
  {
    if y > 0 {
      y := y - 1;
    } else {
      x := x - 1;
      y := b;
    }
  }
}

function fib2(n: nat): nat
  decreases n // аналогично для рекурсивных функций
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

// Массивы
method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key 
    // второе постусловие доказать не полуается
{
  index := 0;
  while index < a.Length
  {
    if a[index] == key { return; }
    index := index + 1;
  }
  index := -1;
}

// Нужно добавить инвариант цикла
method Find2(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall k :: 0 <= k < index ==> a[k] != key
      // c этим сработает
  {
    if a[index] == key { return; }
    index := index + 1;
  }
  index := -1;
}

// Предикаты
predicate sorted1(a: array<int>)
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

predicate sorted(a: array<int>)
  reads a // разрешение читать из памяти (обращаться по индексу)
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

method SetZero(a: array<int>, index: nat)
  requires 0 <= index < a.Length
  modifies a // разрешение писать в память
{
  a[index] := 0;
  return;
}

// Зачем мы требуем явной аннотации reads в предикатах?
method Testing3(a: array<int>, b: array<int>)
  requires sorted(a)
  requires b.Length > 0
  modifies b
  requires a != b
{
  SetZero(b, 0);
  assert sorted(a); // Это проходит потому что Dafny понимает что sorted
                    // зависит только от a (по аннотации reads),
                    // а SetZero выше изменяет только b.
                    // Без аннотаций это было бы намного трудней
}

method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires sorted(a)
  ensures index >= 0 ==> index < a.Length && a[index] == value
  ensures index < 0  ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  var left, right := 0, a.Length;
  while left < right
    invariant 0 <= left <= right <= a.Length
    invariant forall i ::
      0 <= i < a.Length && !(left <= i < right) ==> a[i] != value
  {
    var middle := (left + right) / 2;
    if a[middle] < value {
      left := middle + 1;
    } else if value < a[middle] {
      right := middle;
    } else {
      return middle;
    }
  }
  return -1;
}