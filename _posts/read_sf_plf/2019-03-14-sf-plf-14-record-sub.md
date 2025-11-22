---
published: false
title: "ã€ŒSF-PLFã€?4 RecordSub"
subtitle: "Programming Language Foundations - Subtyping with Records"
layout: post
author: "Hux"
header-style: text
hidden: true
tags:
  - SF (è½¯ä»¶åŸºç¡€)
  - PLF (ç¼–ç¨‹è¯­è¨€åŸºç¡€)
  - Coq
  - ç¬”è®°
---


```coq
Inductive ty : Type :=
  (* record types *)
  | RNil : ty
  | RCons : string â†?ty â†?ty â†?ty.
```

we need typecon to identify record...


```coq
Inductive tm : Type :=
  | rproj ...?  isn't it as well?
  (* record terms *)
  | rnil : tm
  | rcons : string â†?tm â†?tm â†?tm.
``

as a list...


for Record, can compiler reorder the fields? (SML and OCaml)






