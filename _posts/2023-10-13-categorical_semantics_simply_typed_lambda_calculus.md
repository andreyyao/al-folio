---
layout: post
title: Categorical Semantics of Simply Typed Lambda Calculus
date: 2023-10-13 11:12:00-0400
description: Blank
tags: category pl
related_posts: false
toc:
  beginning: true
---

# Introduction
Computer programs are complicated. How do we develop a better understanding of how they work? _Denotational semantics_ is the subarea of programming languages where people study the behaviors of programs by mapping them into some _semantic domain_ of mathematical objects.

The [_lambda calculus_](https://www.cs.cornell.edu/courses/cs6110/2023sp/lectures/lec02.pdf) is one of the simplest programming languages there is. Written in Backus-Naur form (BNF), it only has three kinds of expressions:

$$ e\;:=\;x\;|\;\lambda x.e\;|\;e_1\;e_2 $$

which stands for variable, function abstraction, and function application. Despite its simplicity, the lambda calculus is Turing-complete, and in particular can represent infinite loops. There has been interesting work in giving semantics to the lambda calculus via _domain theory_, but that's the topic for another day.

## Computational trilogy
We will focus our attention on [simply typed lambda calculus](https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus)(STLC). STLC adds types to the (pure) lambda calculus. As a programming language, STLC is _strongly normalizing_, meaning that every well-typed term will eventually evaluate to a normal form. That shouldn't be discouraging, since STLC is closely connected to intuitionistic logic, via the _Curry-Howard correspondence_. It turns out that logic and type systems are both connected to _category theory_ via the so-called _Curry-Howard-Lambek_ correspondence.

The goal of this post is to explicitly spell out a categorical semantics of STLC. I was unable to find proofs for the following table taken from this [nlab page](https://ncatlab.org/nlab/show/computational+trilogy) on "computational trilogy", so I wish to write it down in this blog post.

| logic                | type theory             | category theory                   |
|:--------------------:|:-----------------------:|:---------------------------------:|
| propositions         | types                   | objects                           |
| proofs               | terms                   | /                                 |
| impl-intro           | $$\lambda$$ abstraction | counit from tensor-hom adjunction |
| impl-elim            | application             | unit from tensor-hom adjunction   |
| cut elimination      | $$\beta$$ reduction     | zigzag identities                 |
| identity elimination | $$\eta$$ conversion     | other zigzag                      |

<br>

# Categorical semantics

Some of the following definitions are adapted from Benjamin Pierce's _Basic Category for Computer Scientists_.

## The type theory

We define the grammar for types in STLC:

$$\tau\;:=\;\texttt{Unit}\;|\;\tau_1\to\tau_2\;|\;\tau_1\;\times\;\tau_2$$

And the grammar for terms:

$$e\;:=\;\texttt{unit}\;|\;\lambda x:\tau.e\;|\;e_1\;e_2\;|\;(e_1,e_2)\;|\;\texttt{fst}\;e\;|\;\texttt{snd}\;e$$

Here, $$\texttt{Unit}$$ is the type with one element $$\texttt{unit}$$. we also consider the following typing rules:

<!-- $$ -->
<!-- \begin{prooftree} -->
<!-- \AxiomC{} -->
<!-- \RightLabel{Hyp$^{1}$} -->
<!-- \UnaryInfC{$P$} -->
<!-- \AXC{$P\to Q$} -->
<!-- \RL{$\to_E$} -->
<!-- \BIC{$Q^2$} -->
<!-- \AXC{$Q\to R$} -->
<!-- \RL{$\to_E$} -->
<!-- \BIC{$R$} -->
<!-- \AXC{$Q$} -->
<!-- \RL{Rit$^2$} -->
<!-- \UIC{$Q$} -->
<!-- \RL{$\wedge_I$} -->
<!-- \BIC{$Q\wedge R$} -->
<!-- \RL{$\to_I$$^1$} -->
<!-- \UIC{$P\to Q\wedge R$} -->
<!-- \end{prooftree} -->
<!-- $$ -->

$$
\begin{prooftree}
\AXC{ }
\RightLabel{Unit}
\UIC{$\Gamma\vdash\texttt{unit}:\texttt{Unit}$}
\end{prooftree}
$$

$$
\begin{prooftree}
\AXC{ }
\RightLabel{Var}
\UIC{$\Gamma,x:A\vdash x:A$}
\end{prooftree}
$$

$$
\begin{prooftree}
\AXC{$\Gamma\vdash x:A$}
\RightLabel{Weaken}
\UIC{$\Gamma,y:B\vdash x:A$}
\end{prooftree}
$$

$$
\begin{prooftree}
\AXC{$\Gamma, x:A\vdash e:B$}
\RightLabel{Abs}
\UIC{$\Gamma\vdash\lambda x:A. e:A\to B$}
\end{prooftree}
$$

$$
\begin{prooftree}
\AXC{$\Gamma\vdash f:A\to B$}
\AXC{$\Gamma\vdash e:A$}
\RightLabel{App}
\BIC{$\Gamma\vdash f\;e:B$}
\end{prooftree}
$$

$$
\begin{prooftree}
\AXC{$\Gamma\vdash e:A\times B$}
\RightLabel{fst}
\UIC{$\Gamma\vdash \texttt{fst}\;e:A$}
\end{prooftree}
$$

$$
\begin{prooftree}
\AXC{$\Gamma\vdash e:A\times B$}
\RightLabel{snd}
\UIC{$\Gamma\vdash \texttt{snd}\;e:B$}
\end{prooftree}
$$

$$
\begin{prooftree}
\AXC{$\Gamma\vdash e_1:A$}
\AXC{$\Gamma\vdash e_2:B$}
\RightLabel{pair}
\BIC{$\Gamma\vdash (e_1,e_2):A\times B$}
\end{prooftree}
$$

## A Cartesian-closed category

For the other piece of the translation, we fix any Cartesian-closed category $$\mathbf{C}$$. Recall that a Cartesian-closed category is a category with finite products, such that for each object $$A$$, the _right product functor_ $$(-\times A):\mathbf{C}\to\mathbf{C}$$ has a _right adjoint_ $$-^A:\mathbf{C}\to\mathbf{C}$$ called the exponential.

The definition of adjunctions come with a unit natural transformation $$\epsilon_Y:(-^A\times A)\to \text{Id}_\mathbf{C}$$ and a counit natural transformation $$\eta_Y:\text{Id}_\mathbf{C}\to (-\times A)^A$$ such that