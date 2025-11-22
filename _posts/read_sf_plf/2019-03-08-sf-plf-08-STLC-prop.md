---
published: false
title: "「SF-PLF�? StlcProp"
subtitle: "Programming Language Foundations - Properties of STLC"
layout: post
author: "Hux"
header-style: text
hidden: true
tags:
  - SF (软件基础)
  - PLF (编程语言基础)
  - Coq
  - 笔记
---

基本的定理依赖关�?top-down: 

Type Safety
  - Progress
    - Canonical Forms (one for each type of value)
  - Preservation
    - Substituion
      - Context Invariance (in PLT, Exchange, and Weakening)


Canonical Forms
---------------

对于我们只有 `bool` 一�?base type �?STLC，只需�?`bool` �?`λ`:

```coq
Lemma canonical_forms_bool : ∀t,
  empty �?t �?Bool �?
  value t �?
  (t = tru) �?(t = fls).

Lemma canonical_forms_fun : ∀t T1 T2,
  empty �?t �?(Arrow T1 T2) �?
  value t �?
  ∃x u, t = abs x T1 u.
```



Progress
--------

```coq
Theorem progress : ∀t T,
  empty �?t �?T �?
  value t �?∃t', t --> t'.
```

类似 `Types` 章节�?`progress` �?PLT 中的 proof. 

1. induction on typing relation
2. induction on term

这两个思路的证明基本一致，
  - `auto` 上来就用�?`tru`, `fls`, `abs` 三个 `value` �?case 干掉了，
  - take step �?case 则需�?witness 一�?`t'`, 这时�?Canonical Form 就派上用场了





Preservation
------------

_preservation theorem_ 
  - induction on typing; prove it type-preserving after reduction/evaluation (what about induction on reduction?)
  - `ST_AppAbs` 比较麻烦，需要做 substitution，所以我们需要证�?substituion 本身�?type-preserving...
_substitution lemma_
  - induction on term; prove it type-preserving after a substitution
  - 替换会将 bound var 加入 Context，所以我们需要证�?free var 对于新的 Context 仍然�?type-preserving...
    - 这里我们需�?the formal definition of _free var_ as well.
_context invariance_
  - exchange  : 交换顺序显然无影�?
  - weakening : 如果不是 override 的话，添加新变量显然对于之前�?well-typeness 无影�?


### Free Occurrences

�?PLT/TAPL 中，我们�?"free variables of an term" 定义为一个集�?`FV(t)`. (集合是一�?computational 的概�?

        FV(x) = {x}
    FV(λx.t1) = FV(t1) �?FV(t2)
    FV(t1 t2) = FV(t1) \ {x} 

在这里，我们则将 "appears_free in" 定义�?var `x` �?term `t` 上的二元关系: (读作 judgement 即可)

```coq
Inductive appears_free_in : string �?tm �?Prop :=
  | afi_var : ∀x,
      appears_free_in x (var x)
  | afi_app1 : ∀x t1 t2,
      appears_free_in x t1 �?
      appears_free_in x (app t1 t2)
  | afi_app2 : ∀x t1 t2,
      appears_free_in x t2 �?
      appears_free_in x (app t1 t2)
  | afi_abs : ∀x y T11 t12,
      y �?x �?
      appears_free_in x t12 �?
      appears_free_in x (abs y T11 t12)
  (** 省略 test **)
  ... 

Hint Constructors appears_free_in.

(** a term with no free vars. 等价�?¬(∃x,  appears_free_in x t). **) 
Definition closed (t:tm) :=           ∀x, ¬appears_free_in x t.
```

> An _open term_ is one that _may_ contain free variables.   
> "Open" precisely means "possibly containing free variables."

> the closed terms are a subset of the open ones. 
> closed �?open 的子�?..这样定义吗（


### Free Vars is in Context

首先我们需要一个「free var 都是 well-typed 」的 lemma

```coq
Lemma free_in_context : ∀x t T Gamma,   (** 名字有一�?misleading，意思是 "free vars is in context" 而不�?"var is free in context"... **)
   appears_free_in x t �?
   Gamma �?t �?T �?
   ∃T', Gamma x = Some T'.
```

由此我们可以推论 所有在 empty context �?well typed �?term 都是 closed 得：

```coq
Corollary typable_empty__closed : ∀t T,
    empty �?t �?T �?
    closed t.
```


### Context Invariance 上下文的一些「不变式�?

PLT �?Weaking �?Exchanging 其实就对应了 Gamma 作为 `partial_map` �?`neq` �?`permute`
这里，我们直接进一步地证明 「term �?well-typeness 在『free var 的值不变的 context 变化下』是 preserving 得�? 

```coq
Lemma context_invariance : ∀Gamma Gamma' t T,
    Gamma �?t �?T �?
    (∀x, appears_free_in x t �?Gamma x = Gamma' x) �?   (** <-- 这句的意思是：对�?freevar，我们有其值不变。（如果没有括号就变成所有值都不变了……）**)
    Gamma' �?t �?T.
```


### Substitution!

```coq
Lemma substitution_preserves_typing : ∀Gamma x U t v T,
  (x �? U ; Gamma) �?t �?T �?
  empty �?v �?U �?             (** 这里我们其实 assume 被替换进来的项，即「参数」，�?closed 得。这是一个简化的版本 **)
  Gamma �?[x:=v]t �?T.
```

> 可以被看做一种交换律 ("commutation property")
> 即先 type check �?substitution �?�?substition �?type check 是等价的

Proof by induction on term __不好证，挺麻烦的__


### Finally, Preservation

```coq
Theorem preservation : ∀t t' T,
  empty �?t �?T �?
  t --> t' �?
  empty �?t' �?T.
```


### Not subject expansion

```coq
Theorem not_subject_expansion:
  ~(forall t t' T, t --> t' /\ empty |- t' \in T -> empty |- t \in T).
```

    (app (abs x (Arrow Bool Bool) tru) tru)  -- 考虑 term 

    (λx:Bool->Bool . tru) tru   -->   tru    -- 可以 step
                        empty   |-   Bool    -- step �?well-typed

    empty |-/-  (λx:Bool->Bool . tru) tru    -- 但是�?term 显然 ill-typed




Type Soundness
--------------

```coq
(** stuck 即在不是 value 的时候无�?step **)
Definition stuck (t:tm) : Prop :=
  (normal_form step) t �?¬value t.

(** well-typed term never get stuck! **)
Corollary soundness : ∀t t' T,
  empty �?t �?T �?
  t -->* t' �?
  ~(stuck t').
```



Uniqueness of Types
-------------------

> 这里�?Uniqueness �?Right-unique / deterministic / functional 其实都是相同的内�?

```coq
Theorem unique_types : ∀Gamma e T T',
  Gamma �?e �?T �?
  Gamma �?e �?T' �?
  T = T'.
```





Additional Exercises
--------------------

### STLC with Arithmetic 

> only `Nat`...这样就不用管 the interaction between `Bool` and `Nat` 

```coq
Inductive ty : Type :=
  | Arrow : ty �?ty �?ty
  | Nat : ty.            (** <-- the only concrete base type **)


Inductive tm : Type :=
  | var : string �?tm
  | app : tm �?tm �?tm
  | abs : string �?ty �?tm �?tm
  | const : nat �?tm     (** <-- 居然�?metalang �?nat 而非 zro **)
  | scc : tm �?tm
  | prd : tm �?tm
  | mlt : tm �?tm �?tm
  | test0 : tm �?tm �?tm �?tm.
```

更多拓展见下一�?`MoreStlc.v` 



