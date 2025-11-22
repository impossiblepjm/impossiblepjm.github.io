---
published: false
title: "「SF-PLF�?7 UseTactics"
subtitle: "Programming Language Foundations - Tactic Library For Coq"
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

```coq
From PLF Require Import LibTactics.
```

`LibTactics`  vs. `SSReflect` (another tactics package)

- for PL      vs. for math
- traditional vs. rethinks..so harder


Tactics for Naming and Performing Inversion
-------------------------------------------

### `introv`

```coq
Theorem ceval_deterministic: ∀c st st1 st2,
  st =[ c ]�?st1 �?
  st =[ c ]�?st2 �?
  st1 = st2.
intros c st st1 st2 E1 E2. (* 以往如果想给 Hypo 命名必须说全 *)
introv E1 E2.              (* 现在可以忽略 forall 的部�?*)
```

### `inverts`

```coq
(* was... 需�?subst, clear *)
- inversion H. subst. inversion H2. subst. 
(* now... *)
- inverts H. inverts H2. 


(* 可以�?invert 出来的东西放�?goal 的位置让你自己用 intro 命名�?)
inverts E2 as.
```







Tactics for N-ary Connectives
-----------------------------

> Because Coq encodes conjunctions and disjunctions using binary constructors �?and �?..
> to work with a `N`-ary logical connectives...

### `splits`

> n-ary conjunction

n-ary `split`


### `branch`

> n-ary disjunction

faster `destruct`?






Tactics for Working with Equality
---------------------------------


### `asserts_rewrite` and `cuts_rewrite`


### `substs`

better `subst` - not fail on circular eq


### `fequals`

vs `f_equal`?


### `applys_eq`

variant of `eapply` 





Some Convenient Shorthands
--------------------------


### `unfolds`

better `unfold`


### `false` and `tryfalse`

better `exfalso`


### `gen` 

shorthand for `generalize dependent`, multiple arg.

```coq
(* old *)
intros Gamma x U v t S Htypt Htypv.
generalize dependent S. generalize dependent Gamma.
 
(* new...so nice!!! *)
introv Htypt Htypv. gen S Gamma.
```


### `admits`, `admit_rewrite` and `admit_goal`

wrappers around `admit`


### `sort`

> proof context more readable 

vars       -> top
hypotheses -> bottom







Tactics for Advanced Lemma Instantiation
----------------------------------------


### Working on `lets` 

### Working on `applys`, `forwards` and `specializes`


