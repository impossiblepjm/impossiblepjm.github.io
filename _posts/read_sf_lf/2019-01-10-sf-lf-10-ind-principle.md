---
published: false
title: "「SF-LC�?0 IndPrinciples"
subtitle: "Logical Foundations - Induction Principles"
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


Basic
-----

> 每次我们使用 `Inductive` 来声明数据类型时，Coq 会自动为这个类型生成 _归纳原理_�?
> Every time we declare a new `Inductive` datatype, Coq automatically generates an _induction principle_ for this type. 


自然数的归纳原理:

```coq
Check nat_ind. :

∀ P : nat �?Prop,
  P 0  �?
  (∀ n : nat, P n -> P (S n)) �?
  ∀ n : nat, P n
```

written as inference rule:

                        P 0
      ∀ n : nat, P n -> P (S n)
      -------------------------
      ∀ n : nat,        P n


> `induction` tactic is wrapper of `apply t_ind`


> Coq 为每一�?`Inductive` 定义的数据类型生成了归纳原理，包括那些非递归�?
> Coq generates induction principles for every datatype defined with `Inductive`, including those that aren't recursive. 

> 尽管我们不需要使用归纳来证明非递归数据类型的性质
> Although of course we don't need induction to prove properties of non-recursive datatypes. (`destruct` would be sufficient)

> 归纳原理的概念仍然适用于它们： 它是一种证明一个对于这个类型所有值都成立的性质的方法�?
> the idea of an induction principle still makes sense for them: it gives a way to prove that a property holds for all values of the type.


### Non-recursive

```coq
Inductive yesno : Type :=
  | yes
  | no.

Check yesno_ind. :
yesno_ind : ∀ P : yesno �?Prop,
  P yes  �?
  P no   �?
  ∀ y : yesno, P y 
```

                 P yes 
                 P no
    ------------------
    ∀ y : yesno, P y 


### Structural-Recursive

```coq
Inductive natlist : Type :=
  | nnil
  | ncons (n : nat) (l : natlist).

Check natlist_ind. :
natlist_ind : ∀ P : natlist �?Prop,
  P nnil  �?
  (∀ (n : nat) (l : natlist), P l -> P (ncons n l)) �?
  ∀ l : natlist, P l 
```

                                      P nnil 
    ∀ (n : nat) (l : natlist), P l -> P (ncons n l)
    -----------------------------------------------
    ∀ l : natlist,                    P l 


`P` only need to fullfill `l : the_type` but not `n:nat` since we are proving property of `the_type`.


### The Pattern

> These generated principles follow a similar pattern. 
- induction on each cases 
- proof by exhaustiveness?

```coq
Inductive t : Type := 
  | c1 (x1 : a1) ... (xn : an)
  ...
  | cn ...

t_ind : ∀P : t �?Prop,
              ... case for c1 ... �?
              ... case for c2 ... �?...
              ... case for cn ... �?
              ∀n : t, P n
```

对于 `t` 的归纳原理是又所有对�?`c` 的归纳原理所组成�? （即所�?case 成立)

对于 `c` 的归纳原理则�?
> 对于所有的类型�?`a1...an` 的�?`x1...xn`，如�?`P` 对每�?归纳的参数（每个具有类型 `t` �?`xi`）都成立，那�?`P` 对于 `c x1 ... xn` 成立�?

每个具有类型 `t` 的参数的地方即发生了「递归」与「子结构」，归纳假设 = 「对子结构成立�?





Polymorphism
------------

接下来考虑多态列表：


```coq
(* in ADT syntax *)
Inductive list (X:Type) : Type :=
  | nil 
  | cons (x : X) (l': list X) 

(* in GADT syntax *)
Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X �?list X �?list X.
```

> here, the whole def is _parameterized_ on a `set X`: that is, we are defining a _family_ of inductive types `list X`, one for each `X`.

这里，整个定义都是被集合 `X` _参数化_的： 
也即，我们定义了一个族 `list : X -> Type`, 对于每个 `X`，我们都有一个对应的_项_: `list X`, which is a `Type`, 可写�?`list X : Type`.


> `list_ind` can be thought of as a polymorphic function that, 
> when applied to a type `X`, gives us back an induction principle specialized to the type `list X`.

因此，其归纳定理 `list_ind` 是一个被 `X` 参数化多态的函数�?
当应�?`X : Type` 时，返回一个特化在 `list X : Type` 上的归纳原理


```coq
list_ind : ∀(X : Type) (P : list X �?Prop),
    P [] �?
    (∀(x : X) (l : list X), P l �?P (x :: l)) �?
    ∀l : list X, P l
```

    ∀(X : Type), {

                               P []                   -- base structure holds
        ∀(x : X) (l : list X), P l �?P (x :: l)       -- sub-structure holds -> structure holds
        ---------------------------------------
        ∀l : list X,           P l                    -- all structure holds

    }



Induction Hypotheses 归纳假设
----------------------------


>  The induction hypothesis is the _premise_ of this latter implication 
> �?the assumption that `P` holds of `n'`, which we are allowed to use in proving that `P` holds for `S n'`.

_归纳假设就是 `P n' -> P (S n')` 这个蕴含式中的前提部分_
使用 `nat_ind` 时需要显式得�?`intros n IHn` 引入，于是就变成�?proof context 中的假设.





More on the `induction` Tactic
------------------------------

### "Re-generalize" 重新泛化

Noticed that in proofs using `nat_ind`, we need to keep `n` generailzed. 
if we `intros` particular `n` first then `apply nat_ind`, it won't works...

But we could `intros n. induction n.`, that's `induction` tactic internally "re-generalize" the `n` we perform induction on.


### Automatic `intros` i.e. specialize variables before the variable we induction on

A canonical case is `induction n` vs `induction m` on theorem `plus_comm'' : ∀n m : nat, n + m = m + n.`.
to keep a var generial...we can either change variable order under `∀`, or using `generalize dependent`.





Induction Principles in Prop
----------------------------

### 理解依赖类型的归纳假�?�?Coq 排除证据参数的原�?

除了集合 `Set`，命�?`Prop` 也可以是归纳定义�?`induction` on �?
难点在于：_Inductive Prop_ 通常�?dependent type 的，这里会带来复杂度�?

考虑命题 `even`:

```coq
 Inductive even : nat �?Prop :=
  | ev_0 : even 0
  | ev_SS : ∀n : nat, even n �?even (S (S n)).
```

我们可以猜测一个最 general 的归纳假设：

```coq
ev_ind_max : ∀ P : (∀n : nat, even n �?Prop),
  P O ev_0 �?
  (∀(m : nat) (E : even m), P m E �?P (S (S m)) (ev_SS m E)) �?
  ∀(n : nat) (E : even n), P n E
```

�?


                                       P 0 ev_0                    -- base 
      ∀(m : nat) (E : even m), P m E �?P (S (S m)) (ev_SS m E)     -- sub structure -> structure
      --------------------------------------------------------
      ∀(n : nat) (E : even n),         P n E                       -- all structure


注意这里:

1. `even` is _indexed_ by nat `n` (对比 `list` is _parametrized_ by `X`)
  - 从族的角�?  `even : nat -> Prop`, a family of `Prop` indexed by `nat`
  - 从实体角�? 每个 `E : even n` 对象都是一�?evidence that _particular nat is even_.

2. 要证的性质 `P` is parametrized by `E : even n` 也因此连带着 by `n`. 也就�?`P : (∀n : nat, even n �?Prop)`  (对比 `P : list X �?Prop`)
  - 所以其实关�?`even n` 的性质是同时关于数�?`n` 和证�?`even n` 这两件事�?
  
因此 `sub structure -> structure` 说得是：
> whenever `n` is an even number and `E` is an evidence of its evenness, if `P` holds of `n` and `E`, then it also holds of `S (S n)` and `ev_SS n E`.
> 对于任意数字 `n` 与证�?`E`，如�?`P` �?`n` �?`E` 成立，那么它也对 `S (S n)` �?`ev_SS n E` 成立�?



然而，当我�?`induction (H : even n)` 时，我们通常想证的性质并不包括「证据」，而是「满足该性质的这 `Type` 东西」的性质, 
比如:
1. `nat` 上的一元关�?(性质)    证明 `nat` 的性质          :  `ev_even : even n �?∃k, n = double k`
2. `nat` 上的二元关系           证明 `nat` 上的二元关系    :  `le_trans : ∀m n o, m �?n �?n �?o �?m �?o` 
3. 二元关系 `reg_exp × list T` 证明 二元关系 `reg_exp × T`:  `in_re_match : ∀T (s : list T) (x : T) (re : reg_exp), s =~ re �?In x s �?In x (re_chars re).` 
都是如此�?

因此我们也不希望生成的归纳假设是包括证据�?..
原来的归纳假设：

      ∀P : (∀n : nat, even n �?Prop),
      ... �?
      ∀(n : nat) (E : even n), P n E
      
可以被简化为只对 `nat` 参数化的归纳假设�?

      ∀P : nat �?Prop,
      ... �?
      ∀(n : nat) (E: even n), P n
      

因此 coq 生成的归纳原理也是不包括证据的。注�?`P` 丢弃了参�?`E`:

```coq
even_ind : ∀ P : nat -> Prop,
  P 0 �?
  (∀ n : nat, even n -> P n -> P (S (S n))) �?
  ∀ n : nat, even n -> P n *)
```

用人话说就是�?
1. P �?0 成立�?
2. 对任�?n，如�?n 是偶数且 P �?n 成立，那�?P �?S (S n) 成立�?
=> P 对所有偶数成�?


### "General Parameter"

```coq
Inductive le : nat �?nat �?Prop :=
  | le_n : ∀ n,               le n n
  | le_S : ∀ n m, (le n m) �?(le n (S m)).
```

```coq
Inductive le (n:nat) : nat �?Prop :=
  | le_n                : le n n
  | le_S m (H : le n m) : le n (S m).
```

两者虽然等价，但是共同�?`∀ n` 可以被提升为 typecon 的参�? i.e. "General Parameter" to the whole definition.

其生成的归纳假设也会不同: (after renaming)

```coq
le_ind : ∀ P : nat -> nat -> Prop,
  (∀ n : nat, P n n) ->
  (∀ n m : nat, le n m -> P n m -> P n (S m)) ->
  ∀ n m : nat, le n m -> P n m 
```

```coq
le_ind : ∀ (n : nat) (P : nat -> Prop),
  P n ->
  (∀ m : nat, n <= m -> P m -> P (S m)) ->
  ∀ m : nat, n <= m -> P m 
```

The 1st one looks more symmetric but 2nd one is easier (for proving things).


