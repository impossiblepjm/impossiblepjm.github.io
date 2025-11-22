---
published: false
title: "「SF-LC�?5 Extraction"
subtitle: "Logical Foundations - Extracting ML From Coq"
layout: post
author: "Hux"
header-style: text
hidden: true
tags:
  - LF (逻辑基础)
  - SF (软件基础)
  - Coq
  - 笔记
---


Basic Extraction
----------------

- OCaml   (most mature)
- Haskell (mostly works)
- Scheme  (a bit out of date)

```coq
Extraction "imp1.ml" ceval_step.
```

When Coq processes this command:

```
The file imp1.ml has been created by extraction.
The file imp1.mli has been created by extraction.
```



Controlling Extraction of Specific Types
----------------------------------------

如果不做任何处理的话...生成�?`ml` 里的 `nat` 则都会是 Church Numeral...

> We can tell Coq how to extract certain `Inductive` definitions to specific OCaml types.
> we must say:
> 1. how the Coq type itself should be represented in OCaml
> 2. how each constructor should be translated

```coq
Extract Inductive bool �?"bool" [ "true" "false" ].
```

> also, for non-enumeration types (where the constructors take arguments), 
> we give an OCaml expression that can be used as a _"recursor"_ over elements of the type. (Think Church numerals.)

```coq
Extract Inductive nat �?"int"
  [ "0" "(fun x �?x + 1)" ]
  "(fun zero succ n �?
      if n=0 then zero () else succ (n-1))".
```

```coq
Extract Constant plus �?"( + )".
Extract Constant mult �?"( * )".
Extract Constant eqb �?"( = )".
```

> 注意：保证提取结果的合理性是你的责任�?

```coq
Extract Constant minus �?"( - )".
```

比如这么做很诱人……但是我�?Coq 的定义里 `0 - 1 = 0`, OCaml �?`int` 则会有负�?..



### Recursor 的理论与实现 - a "encoding" of case expression and sum type

```coq
Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
```
```ocaml
let rec ceval_step st c = function
  | O -> None
  | S i' ->
    (match c with
```
```ocaml
let rec ceval_step st c i =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> None)     (* zero *)
    (fun i' ->          (* succ *)
    match c with
```

注意我们是如何使�?"recursor" 来替�?`case`, `match`, pattern matching 得�?

recall _sum type_ �?PLT 中的语法与语义：

```coq
T ::= 
  T + T

e ::=
  case e of
    | L(e) => e
    | R(e) => e

```
```
                      e �?e' 
                  ------------- (work inside constructor)
                  C(e) -> C(e')

                      e �?e' 
          -------------------------------   (work on the expr match against)
          case e of ... �? case e' of ...

     -----------------------------------------------  (match Left constructor, substitute)
     case L(v) of L(x) => e1 | R(y) => e2 �?e1 [v/x]

     -----------------------------------------------  (match Right constructor, substitute)
     case R(v) of L(x) => e1 | R(y) => e2 �?e1 [v/x]
```

可以发现 `case` 表达式可以理解为一种特殊的 application，会将其 argument 根据某种 tag （这里为构造函数） apply 到对应的 case body 上，
每个 case body 都是�?lambda abstraction 同构的一�?binder�?

     L(x) => e1     ===   λx.e1
     R(x) => e2     ===   λx.e2 

     case v e1|e2   ===   (λx.e1|e2) v      -- `e1` or `e2` depends on the _tag_ wrapped on `v`
   
这个角度也解释了 Haskell/SML 在申明函数时直接对参数写 pattern match 的理论合理�?

根据经验几乎所有的 _binding_ 都可以被 desugar 成函数（�?lambda expression).
难点在于我们如何 re-implement 这个 _tag_ �?_switch_ 机制?

对于 `Inductive nat` 翻译�?OCaml `int` 时，这个机制可以�?`v =? 0` 来判断，因此我们�?_recursor_ 实现�?

```ocaml
fun zero succ                (* partial application  *)
  n -> if n=0                (* 判断 tag ... *)
       then zero ()          (* 0   case =>  (λx.e1) v *)
       else succ (n-1)       (* S n case =>  (λx.e2) v *)
```







