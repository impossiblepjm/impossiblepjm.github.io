---
published: false
title: "「SF-PLF�? MoreStlc"
subtitle: "Programming Language Foundations - More on The Simply Typed Lambda-Calculus"
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

> make the STLC into a PL!



Simple Extensions to STLC
-------------------------

> 其实这一部分我好像没有任何必要做笔记…�?


### Numbers

See `StlcProp.v` exercise `stlc_arith`.



### Let Bindings

- In PLT slide, we treat `let x   = t1 in e` as a derived form of `(λx   . e) t1`.
- In PLT langF, we treat `let x:T = t1 in e` as a derived form of `(λx:T . e) t1`. (both require explicit type annotation)

SF here, same as TaPL, treat it _less derived_ by _compute the type `T1` from `t1`. 
- but TaPL treat it by desugar to `λ` later on, here we directly "execute" it via substituion.

我想这里有一个原因是�?`λ` 必须要可以独立被 typed，但是这时候我们还没有 `t1`，无法计算出 `T1`。�?`let` 的形式中包括�?`t1`，所以可以直接计�?

```coq
t ::=                Terms
    | ...
    | let x=t in t      let-binding
```

    Reduction:

                                 t1 --> t1'
                     ----------------------------------               (ST_Let1)
                     let x=t1 in t2 --> let x=t1' in t2

                        ----------------------------              (ST_LetValue)  <-- substitute as λ
                        let x=v1 in t2 --> [x:=v1]t2

    Typing:

             Gamma |- t1 \in T1      x|->T1; Gamma |- t2 \in T2
             --------------------------------------------------        (T_Let)
                        Gamma |- let x=t1 in t2 \in T2



### Pairs (Product Type)


```coq
t ::=                Terms
    | ...
    | (t,t)             pair
    | t.fst             first projection
    | t.snd             second projection

v ::=                Values
    | ...
    | (v,v)             pair value

T ::=                Types
    | ...
    | T * T             product type
```

    Reduction:

                              t1 --> t1'
                         --------------------                        (ST_Pair1)
                         (t1,t2) --> (t1',t2)

                              t2 --> t2'
                         --------------------                        (ST_Pair2)
                         (v1,t2) --> (v1,t2')

                              t1 --> t1'
                          ------------------                          (ST_Fst1)
                          t1.fst --> t1'.fst

                          ------------------                       (ST_FstPair)
                          (v1,v2).fst --> v1

                              t1 --> t1'
                          ------------------                          (ST_Snd1)
                          t1.snd --> t1'.snd

                          ------------------                       (ST_SndPair)
                          (v1,v2).snd --> v2


    Typing:

               Gamma |- t1 \in T1     Gamma |- t2 \in T2
               -----------------------------------------               (T_Pair)
                       Gamma |- (t1,t2) \in T1*T2

                        Gamma |- t \in T1*T2
                        ---------------------                          (T_Fst)
                        Gamma |- t.fst \in T1

                        Gamma |- t \in T1*T2
                        ---------------------                          (T_Snd)
                        Gamma |- t.snd \in T2



### Unit (Singleton Type) 单元类型

`unit` is the only value/normal form of type `Unit`, but not the only term (also any terms that would reduce to `unit`)


```coq
t ::=                Terms
    | ...
    | unit              unit              -- often written `()` as well

v ::=                Values
    | ...
    | unit              unit value

T ::=                Types
    | ...
    | Unit              unit type         -- Haskell even write this `()`
```

    No reduction rule!

    Typing:

                         ----------------------                        (T_Unit)
                         Gamma |- unit \in Unit


> wouldn't every computation _living in_ such a type be trivial?
> 难道不是每个计算都不会在这样的类型中_居留_吗？

> Where Unit really comes in handy is in richer languages with side effects
> 在更丰富的语言中，使用 Unit 类型来处理副作用（side effect�?会很方便



### Sum Type (Disjointed Union)

> deal with values that can take two distinct forms -- binary sum type
> 两个截然不同�?... "二元�?类型

> We create elements of these types by _tagging_ elements of the component types
> 我们在创建这些类型的值时，会为值_标记_上其"成分"类型

标签 `inl`, `inr` 可以看做为函数，�?_Data Constructor_

    inl : Nat  -> Nat + Bool
    inr : Bool -> Nat + Bool

> that _"inject"_ (注入) elements of `Nat` or `Bool` into the left and right components of the sum type `Nat+Bool`

不过这里并没有把他们作为 function 来形式化，而是�?`inl` `inr` 作为关键字，�?`inl t` `inr t` 作为 primitive syntactic form...


- In PLT slide, we use `L          (e)` and say the `T2` would be "guessed" to produce `T1 + T2`, as _TaPL option 1_
- In PLT langF, we use `L [T1 +T2] (e)` i.e. provide a explicit type annotation for the sum type, as _TaPL option 3_ (ascription)

SF here, use something in the middle: 
- you provide only `T2` to `L(t1)` and `T1` would be computed from `t1` to form the `T1 + T2`. 


```coq
t ::=                Terms
    | ...
    | inl T t           tagging (left)
    | inr T t           tagging (right)
    | case t of         case
        inl x => t
      | inr x => t

v ::=                Values
    | ...
    | inl T v           tagged value (left)
    | inr T v           tagged value (right)

T ::=                Types
    | ...
    | T + T             sum type
```

    Reduction:

                               t1 --> t1'
                        ------------------------                       (ST_Inl)
                        inl T2 t1 --> inl T2 t1'

                               t2 --> t2'
                        ------------------------                       (ST_Inr)
                        inr T1 t2 --> inr T1 t2'

                               t0 --> t0'
               -------------------------------------------            (ST_Case)
                case t0 of inl x1 => t1 | inr x2 => t2 -->
               case t0' of inl x1 => t1 | inr x2 => t2

            -----------------------------------------------        (ST_CaseInl)
            case (inl T2 v1) of inl x1 => t1 | inr x2 => t2
                           -->  [x1:=v1]t1

            -----------------------------------------------        (ST_CaseInr)
            case (inr T1 v2) of inl x1 => t1 | inr x2 => t2
                           -->  [x2:=v1]t2

    Typing:

                          Gamma |- t1 \in T1
                   ------------------------------                       (T_Inl)
                   Gamma |- inl T2 t1 \in T1 + T2

                          Gamma |- t2 \in T2
                   -------------------------------                      (T_Inr)
                    Gamma |- inr T1 t2 \in T1 + T2

                        Gamma |- t \in T1+T2
                     x1|->T1; Gamma |- t1 \in T
                     x2|->T2; Gamma |- t2 \in T
         ----------------------------------------------------          (T_Case)
         Gamma |- case t of inl x1 => t1 | inr x2 => t2 \in T



### Lists


> The typing features we have seen can be classified into 
> - 基本类型   _base types_ like `Bool`, and
> - 类型构造子 _type constructors_ like `→` and `*` that build new types from old ones.

> In principle, we could encode lists using pairs, sums and _recursive types_. (and _type operator_ to give the type a name in SystemFω)

> 但是 recursive type �?non-trivial 了……于是我们直接处理为一个特殊的类型�?

- in PLT slide, again, we omit the type and simply write `nil : List T`
  - 有趣的是, Prof.Mtf 并不满意这个，因为会�?`hd nil` 这样 stuck 的可能，所以额外给了一个用 `unlist` (unempty list) �?def

- in PLT langF, we did use pairs + sums + recursive types: 
  - langF `nil : all('a . rec('b . unit + ('a * 'b)))`
  - StlcE `nil : ∀α     . µβ     . unit + (α �?β)` 

- in TaPL ch11, we manually provide `T` to all term (data constructor)
  - but actually, only `nil` need it! (others can be inferred by argument)
  
and that's we did for SF here! 


```coq
t ::=                Terms
    | ...
    | nil T                          -- nil need explicit type annotation
    | cons t t
    | lcase t of nil  => t           -- a special case for list
               | x::x => t

v ::=                Values
    | ...
    | nil T             nil value
    | cons v v          cons value

T ::=                Types
    | ...
    | List T            list of Ts
```

    Reduction:

                                t1 --> t1'
                       --------------------------                    (ST_Cons1)
                       cons t1 t2 --> cons t1' t2

                                t2 --> t2'
                       --------------------------                    (ST_Cons2)
                       cons v1 t2 --> cons v1 t2'

                              t1 --> t1'
                -------------------------------------------         (ST_Lcase1)
                 (lcase t1 of nil => t2 | xh::xt => t3) -->
                (lcase t1' of nil => t2 | xh::xt => t3)

               -----------------------------------------          (ST_LcaseNil)
               (lcase nil T of nil => t2 | xh::xt => t3)
                                --> t2

            ------------------------------------------------     (ST_LcaseCons)
            (lcase (cons vh vt) of nil => t2 | xh::xt => t3)
                          --> [xh:=vh,xt:=vt]t3                  -- multiple substi


    Typing:

                        -------------------------                       (T_Nil)
                        Gamma |- nil T \in List T

             Gamma |- t1 \in T      Gamma |- t2 \in List T
             ---------------------------------------------             (T_Cons)
                    Gamma |- cons t1 t2 \in List T

                        Gamma |- t1 \in List T1
                        Gamma |- t2 \in T
                (h|->T1; t|->List T1; Gamma) |- t3 \in T
          ---------------------------------------------------         (T_Lcase)
          Gamma |- (lcase t1 of nil => t2 | h::t => t3) \in T




### General Recursion (Fixpoint)

通用的递归，而非 primitive recursion (PFPL)

```hs
fact = \x:Nat . if x=0 then 1 else x * (fact (pred x)))
```

这个�?Stlc 中不被允许，因为我们在定�?`fact` 的过程中发现了一�?free �?`fact`，要么未定义，要么不是自己�?
所以我们需�?`Fixpoint` 

```hs
fact = fix (\fact:Nat->Nat. 
       \x:Nat . if x=0 then 1 else x * (fact (pred x)))
```


```coq
t ::=                Terms
    | ...
    | fix t             fixed-point operator
```

   Reduction:

                                t1 --> t1'
                            ------------------                        (ST_Fix1)
                            fix t1 --> fix t1'

               --------------------------------------------         (ST_FixAbs)
               fix (\xf:T1.t2) --> [xf:=fix (\xf:T1.t2)] t2         -- fix f = f (fix f)

   Typing:

                           Gamma |- t1 \in T1->T1
                           ----------------------                       (T_Fix)
                           Gamma |- fix t1 \in T1



### Records 

这里的定义非�?informal:


```coq
t ::=                          Terms
    | ...
    | {i1=t1, ..., in=tn}         record
    | t.i                         projection

v ::=                          Values
    | ...
    | {i1=v1, ..., in=vn}         record value

T ::=                          Types
    | ...
    | {i1:T1, ..., in:Tn}         record type
```

    Reduction:

                              ti --> ti'
                 ------------------------------------                  (ST_Rcd)
                     {i1=v1, ..., im=vm, in=ti , ...}
                 --> {i1=v1, ..., im=vm, in=ti', ...}

                              t1 --> t1'
                            --------------                           (ST_Proj1)
                            t1.i --> t1'.i

                      -------------------------                    (ST_ProjRcd)
                      {..., i=vi, ...}.i --> vi

    Typing:

            Gamma |- t1 \in T1     ...     Gamma |- tn \in Tn
          ----------------------------------------------------          (T_Rcd)
          Gamma |- {i1=t1, ..., in=tn} \in {i1:T1, ..., in:Tn}

                    Gamma |- t \in {..., i:Ti, ...}
                    -------------------------------                    (T_Proj)
                          Gamma |- t.i \in Ti


### 其他

提了一�?

- Variant 
- Recursive type `μ`

加起来就可以 
> give us enough mechanism to build _arbitrary inductive data types_ like lists and trees from scratch 

Basically 

ADT = Unit + Product + Sum (Variant) + Function (Expo)

但是 Coq �?`Inductive` 还需要进一步的 Pi (Dependent Product), Sigma (Dependent Sum).




Exercise: Formalizing the Extensions
------------------------------------

### STLCE definitions

基本上就是把上面�?rule �?AST 写进�?



### STLCE examples

> a bit of Coq hackery to automate searching for typing derivation

基本上就是自动化�?pattern matching + tactics

```coq
Hint Extern 2 (has_type _ (app _ _) _) =>
  eapply T_App; auto.

Hint Extern 2 (has_type _ (tlcase _ _ _ _ _) _) =>
  eapply T_Lcase; auto.

Hint Extern 2 (_ = _) => compute; reflexivity.
```


效果非常酷：typecheck 只需�?`eauto`，reduction 只需�?`normalize`.















