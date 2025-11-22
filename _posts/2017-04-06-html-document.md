---
published: false
layout: post
title: 如何理解 <code>document</code> 对象�?<code>HTMLDocument</code> 的实例？
subtitle: Why is <code>document</code> an instance of <code>HTMLDocument</code>?
author: "Hux"
header-style: text
tags:
  - Web
  - 知乎
---

> 这篇文章转载自[我在知乎上的回答](https://www.zhihu.com/question/57601873/answer/155685476)

谢邀�?

首先要理解的�?DOM �?API，是一组无关编程语言的接口（Interfaces）而非实现（Implementation）。前端平时常说的 DOM 其实只是浏览器通过 ECMAScript（JavaScript）对 DOM 接口的一种实现�?

其次要知道的是，DOM 既是�?HTML 制定的，也是�?XML 制定的。而两者各有一些特异的部分，所以作�?DOM 标准基石�?DOM Level 1 其实分为 Core �?HTML 两个部分。Core 定义�?fundamental interfaces �?extended interfaces，分别是共用的基础接口�?「XML 拓展包」，�?HTML 部分则全都是「HTML 拓展包」。题主所问到�?Document 接口被定义在 Core �?fundamental interfaces 中，�?HTMLDocument 接口则定义在 HTML 部分中，且「接口继承」于 Document�?

这种继承关系当然是可以在 JavaScript �?DOM 实现中体现出来的�?

```js
// document �?HTMLDocument 的实�?
document instanceof HTMLDocument // true

// document �?[[prototype]] 指向 HTMLDocument 的原�?
document.__proto__ === HTMLDocument.prototype // true

// HTMLDocument 伪类继承�?Document
HTMLDocument.prototype instanceof Document // true
HTMLDocument.prototype.__proto__ === Document.prototype // true
```

至于 Document �?HTMLDocument 这两个构造函数，�?Array、Object 一样都�?built-in 的：

```js
> Document
< function Document() { [native code] }
> HTMLDocument
< function HTMLDocument() { [native code] }
```

虽然�?native code，但一个有意思的现象是，这两个构造函数之间也是存在原型链的：

```js
// HTMLDocument �?[[prototype]] 是指�?Document �?
HTMLDocument.__proto__ == Document

// 同理
Document.__proto__ == Node
Node.__proto__ == EventTarget
```

其作用是实现对静态成员的继承。（ ES6 Class 的行为与此完全一致，但这个行为在更早之前就是这样了。）

好了扯远了，总结一下，**�?JavaScript �?DOM 实现�?*

*   document �?HTMLDocument 的实�?
*   HTMLDocument 继承�?Document

留一个课后作业，有兴趣的话可以看�?Document.prototype �?HTMLDocument.prototype 里分别都有什么？在不同浏览器里都试试�?

以上�?

