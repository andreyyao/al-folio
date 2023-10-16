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
\quad
\begin{prooftree}
\AXC{$\Gamma\vdash e:A$}
\RightLabel{Weaken}
\UIC{$\Gamma,y:B\vdash e:A$}
\end{prooftree}
$$

$$
\begin{prooftree}
\AXC{$\Gamma, x:A\vdash e:B$}
\RightLabel{Abs}
\UIC{$\Gamma\vdash\lambda x:A. e:A\to B$}
\end{prooftree}
\quad
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
\quad
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

For the other piece of the translation, we fix any Cartesian-closed category (CCC) $$\mathbf{C}$$. Recall that a Cartesian-closed category is a category with finite products, such that for each object $$A$$, the _right product functor_ $$(-\times A):\mathbf{C}\to\mathbf{C}$$ has a right adjoint $$(-^A):\mathbf{C}\to\mathbf{C}$$ called the _exponential_.

The definition of adjunctions come with a unit natural transformation $$\epsilon_A:(-^A\times A)\to \text{Id}_\mathbf{C}$$ and a counit natural transformation $$\eta_A:\text{Id}_\mathbf{C}\to (-\times A)^A$$ such that the following "zigzag" equalities hold:

$$\begin{equation}\mathcal{Id}_{(-\times A)}=\epsilon_A (-\times A)\circ (-\times A)\eta_A\end{equation}$$

$$\begin{equation}\mathcal{Id}_{(-^A)}=(-^A)\epsilon_A\circ \eta_A (-^A)\end{equation}$$

Here $$\text{Id}_\mathbf{C}$$ is the identity functor on $$\mathbf{C}$$, and the caligraphic $$\mathcal{Id}$$ denotes identity natural transformations on the respective functors.

For each object $$B\in\mathbf{C}$$, the component $$\epsilon_{A,B}$$ of the unit $$\epsilon_A$$ has the universal property such that, for any $$C\in\mathbf{C}$$ and morphism $$f$$ from $$(\underline{C}\times A)$$ (the product functor applied to $$C$$) to $$B$$, there exists a unique morphism $$curry(f)$$ from $$C$$ to $$B^A$$ (the exponential functor applied to $$B$$) making the diagram commute:
<div align="center">
<!-- https://q.uiver.app/#q=WzAsMyxbMCwwLCJcXHVuZGVybGluZXtDfVxcdGltZXMgQSJdLFswLDIsIkJeQVxcdGltZXMgQSJdLFsyLDIsIkIiXSxbMSwyLCJcXGVwc2lsb25fe0EsQn0iLDJdLFswLDEsIlxcZXhpc3RzIVxcO2N1cnJ5KGYpXFx0aW1lcyBcXHRleHR7aWR9X0EiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbMCwyLCJmIl1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMyxbMCwwLCJcXHVuZGVybGluZXtDfVxcdGltZXMgQSJdLFswLDIsIkJeQVxcdGltZXMgQSJdLFsyLDIsIkIiXSxbMSwyLCJcXGVwc2lsb25fe0EsQn0iLDJdLFswLDEsIlxcZXhpc3RzIVxcO2N1cnJ5KGYpXFx0aW1lcyBcXHRleHR7aWR9X0EiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbMCwyLCJmIl1d&embed" width="420" height="400" style="border-radius: 8px; border: none;"></iframe>
</div>

Dually, for each object $$C\in\mathbf{C}$$, the component $$\eta_{A,C}$$ of the counit has the universal property that for any $$B\in\mathbf{C}$$ and morphism $$g$$ from $$C$$ to $$\underline{B}^A$$, there exists a unique morphism $$uncurry(g)$$ such that $$(uncurry(g))^A\circ\eta_{A,C}=g$$

## The translation
We are finally ready to define the semantic translation! The double brackets $$[\![\;]\!]$$ takes something from the type theory and maps it into the CCC we specified. On types, it is defined inductive on the syntax and maps each type to an object in the CCC. Again, the following translations are taken from Pierce's _Basic Category for Computer Scientists_:

$$\begin{align*}
[\![\texttt{Unit}]\!]&\triangleq 1_\mathbf{C}\\
[\![A\times B]\!]&\triangleq [\![A]\!] \times [\![B]\!]\\
[\![A\to B]\!]&\triangleq [\![B]\!]^{[\![A]\!]}
\end{align*}$$

The translation for the typing context is inductively defined on the number of variables: $$[\![\varnothing]\!]\triangleq 1_\mathbf{C}$$ and $$[\![\Gamma,x:A]\!]\triangleq [\![\Gamma]\!]\times [\![A]\!]$$.

Finally, we inductively define the translation on the typing derivations:

| Derivation                                           | Translation                                                                                     | Domain                            | Target                            |
|------------------------------------------------------|-------------------------------------------------------------------------------------------------|-----------------------------------|-----------------------------------|
| $$[\![\Gamma\vdash \texttt{unit}:\texttt{Unit}]\!]$$ | $$!_{[\![\Gamma]\!]}$$                                                                          | $$[\![\Gamma]\!]$$                | $$1_\mathbf{C}$$                  |
| $$[\![\Gamma,x:A\vdash x:A]\!]$$                     | $$\pi_2$$                                                                                       | $$[\![\Gamma]\!]\times[\![A]\!]$$ | $$[\![A]\!]$$                     |
| $$[\![\Gamma,y:B\vdash e:A]\!]$$                     | $$[\![\Gamma\vdash e:A]\!]\circ\pi_1$$                                                          | $$[\![\Gamma]\!]\times[\![A]\!]$$ | $$[\![B]\!]$$                     |
| $$[\![\Gamma\vdash \lambda x:A.e:A\to B]\!]$$        | $$curry([\![\Gamma,x:A\vdash e:B]\!])$$                                                         | $$[\![\Gamma]\!]$$                | $$[\![B]\!]^{[\![A]\!]}$$         |
| $$[\![\Gamma\vdash e_1\;e_2:B]\!]$$                  | $$\epsilon_{A,B}\circ\langle[\![\Gamma\vdash e_1:A\to B]\!],[\![\Gamma\vdash e_2:A]\!]\rangle$$ | $$[\![\Gamma]\!]$$                | $$[\![B]\!]$$                     |
| $$[\![\Gamma\vdash (e_1,e_2):A\times B]\!]$$         | $$\langle[\![\Gamma\vdash e_1:A]\!],[\![\Gamma\vdash e_2:B]\!]\rangle$$                         | $$[\![\Gamma]\!]$$                | $$[\![A]\!]\times[\![B]\!]$$ |
| $$[\![\Gamma\vdash \texttt{fst}\;e:A]\!]$$           | $$\pi_1\circ [\![\Gamma\vdash (e_1,e_2):A\times B]\!]$$                                         | $$[\![\Gamma]\!]$$                | $$[\![A]\!]$$                     |
| $$[\![\Gamma\vdash \texttt{snd}\;e:B]\!]$$           | $$\pi_2\circ [\![\Gamma\vdash (e_1,e_2):A\times B]\!]$$                                         | $$[\![\Gamma]\!]$$                | $$[\![B]\!]$$                     |

<br>

For this particular formulation of STLC, it just so happens that for any fixed context, if a term is typeable then there is a unique typing rule that applies to it. This can be seen just from the fact that each term grammar branch appears in the conclusion of exactly one typing rule. Thus, we can be a little hand-wavy and define the translations on the term syntax directly.

# Semantics respects equivalence

## Eta-equivalence
The $$\eta$$-equivalence says that for whatever types $$A,B$$, a function $$h:A\to B$$ should be considered "the same" as $$\lambda x:A. h\;x$$. Indeed, the latter seems to be just "$$h$$ with extra steps". It turns out our categorical interpretation respects this equivalence.

Now for the proof. Suppose $$\Gamma\vdash \lambda x:A.e\;x:A\to B$$. Then $$e$$ must be of type $$A\to B$$, but it doesn't have to be in normal form. Here we "cheat" a bit and assume that we never reuse variable names. That is, $$x$$ should not be a free variable in $$e$$. This is a reasonable assumption though. The semantics of the typing derivations defined earlier tells us

$$\begin{align*}
&[\![\Gamma\vdash \lambda x:A.e\;x:A\to B]\!]\\
=&curry([\![\Gamma,x:A \vdash e\;x:B]\!])\\
=&curry(\epsilon_{A,B}\circ \langle[\![\Gamma,x:A\vdash e:A\to B]\!],[\![\Gamma,x:A\vdash x:A]\!]\rangle)\\
=&curry(\epsilon_{A,B}\circ \langle[\![\Gamma,x:A\vdash e:A\to B]\!],\pi_2\rangle)\\
=&curry(\epsilon_{A,B}\circ \langle[\![\Gamma\vdash e:A\to B]\!]\circ\pi_1,\pi_2\rangle)
\end{align*}$$

Tho a mouthful, $$\epsilon_{A,B}\circ\langle[\![\Gamma\vdash e:A\to B]\!]\circ\pi_1,\pi_2\rangle$$ is a morphism from $$[\![\Gamma]\!]\times [\![A]\!]$$ to $$[\![B]\!]$$. If we set $$C$$ to be $$[\![\Gamma]\!]$$, and $$f$$ as $$\epsilon_{A,B}\circ\langle[\![\Gamma\vdash e:A\to B]\!]\circ\pi_1,\pi_2\rangle$$, then the diagram for the unit equation becomes

<div align="center">
<!-- https://q.uiver.app/#q=WzAsMyxbMCwwLCJbXFwhW1xcR2FtbWFdXFwhXVxcdGltZXMgW1xcIVtBXVxcIV0iXSxbMCwyLCJbXFwhW0JdXFwhXV57W1xcIVtBXVxcIV19XFx0aW1lcyBbXFwhW0FdXFwhXSJdLFsyLDIsIltcXCFbQl1cXCFdIl0sWzEsMiwiXFxlcHNpbG9uX3tBLEJ9IiwyXSxbMCwxLCJnIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzAsMiwiZiJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMyxbMCwwLCJbXFwhW1xcR2FtbWFdXFwhXVxcdGltZXMgW1xcIVtBXVxcIV0iXSxbMCwyLCJbXFwhW0JdXFwhXV57W1xcIVtBXVxcIV19XFx0aW1lcyBbXFwhW0FdXFwhXSJdLFsyLDIsIltcXCFbQl1cXCFdIl0sWzEsMiwiXFxlcHNpbG9uX3tBLEJ9IiwyXSxbMCwxLCJnIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzAsMiwiZiJdXQ==&embed" width="400" height="400" style="border-radius: 8px; border: none;"></iframe>
</div>

Where did the mystery $$g$$ come from? Well, since $$f$$ is of the form $$\epsilon_{A,B}$$ composed with _something_, we can just define $$g$$ to be the _something_, aka $$\langle[\![\Gamma\vdash e:A\to B]\!]\circ\pi_1,\pi_2\rangle$$, and the above diagram will trivially commute. But, note $$g$$ actually equal to $$[\![\Gamma\vdash e:A\to B]\!]\times \text{id}_{[\![A]\!]}$$.

Finally, for the real kicker, we invoke the uniqueness of $$curry$$ in the universal property of $$\epsilon_A$$, so that $$[\![\Gamma\vdash e:A\to B]\!]=curry(\epsilon_{A,B}\circ \langle[\![\Gamma\vdash e:A\to B]\!]\circ\pi_1,\pi_2\rangle)$$. This concludes the proof that our categorical semantics respects eta-equivalence:

$$[\![\Gamma\vdash \lambda x:A.e\;x:A\to B]\!]=[\![\Gamma\vdash e:A\to B]\!]$$

# Conclusion
