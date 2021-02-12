\documentclass{article}

\usepackage{fontspec}
\usepackage{fullpage}
\usepackage{hyperref}
\usepackage{agda}

\usepackage{unicode-math}


\setmainfont{DejaVu Serif}
\setsansfont{DejaVu Sans}
\setmonofont{DejaVu Sans Mono}

% \setmonofont{Fira Mono}
% \setsansfont{Noto Sans}

\usepackage{newunicodechar}

\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}

\newtheorem{definition}{Definition}


\author{Warrick Macmillan}
\title{Roadmap}

\begin{document}

\maketitle

\section{Introduction}

The central concern of this thesis is the syntax of mathematics, programming
languages, and their respective mutual influence, as conceived and practiced by
mathematicians and computer scientists.  From one vantage point, the role of
syntax in mathematics may be regarded as a 2nd order concern, a topic for
discussion during a Fika, an artifact of ad hoc development by the working
mathematician whose real goals are producing genuine mathematical knowledge.
For the programmers and computer scientists, syntax may be regarding as a
matter of taste, with friendly debates recurring regarding the use of
semicolons, brackets, and white space.  Yet, when viewed through the lens of
the propositions-as-types paradigm, these discussions intersect in new and
interesting ways.  When one introduces a third paradigm through which to
analyze the use of syntax in mathematics and programming, namely Linguistics, I
propose what some may regard as superficial detail, indeed becomes a central
paradigm, with many interesting and important questions. 

To get a feel for this syntactic paradigm, let us look at a basic mathematical
example: that of a group homomorphism, as expressed in a variety of sources.  

% Wikipedia Defn:

\begin{definition}
In mathematics, given two groups, $(G, \ast)$ and $(H, \cdot)$, a group homomorphism from $(G, \ast)$ to $(H, \cdot)$ is a function $h : G \to H$ such that for all $u$ and $v$ in $G$ it holds that

\begin{center}
  $h(u \ast v) = h ( u ) \cdot h ( v )$ 
\end{center}
\end{definition}

% http://math.mit.edu/~jwellens/Group%20Theory%20Forum.pdf

\begin{definition}
Let $G = (G,\cdot)$ and $G' = (G',\ast)$ be groups, and let $\phi : G \to G'$ be a map between them. We call $\phi$ a \textbf{homomorphism} if for every pair of elements $g, h \in G$, we have 
\begin{center}
  $\phi(g \ast h) = \phi ( g ) \cdot \phi ( h )$ 
\end{center}
\end{definition}

% http://www.maths.gla.ac.uk/~mwemyss/teaching/3alg1-7.pdf

\begin{definition}
Let $G$, $H$, be groups.  A map $\phi : G \to H$ is called a \emph{group homomorphism} if
\begin{center}
  $\phi(xy) = \phi ( x ) \phi ( y )$ for all $x, y \in G$ 
\end{center}
(Note that $xy$ on the left is formed using the group operation in $G$, whilst the product $\phi ( x ) \phi ( y )$ is formed using the group operation $H$.)
\end{definition}

% NLab:

\begin{definition}
Classically, a group is a monoid in which every element has an inverse (necessarily unique).
\end{definition}

We inquire the reader to pay attention to nuance and difference in presentation
that is normally ignored or taken for granted by the fluent mathematician.
These all mean the same thing--don't they?  This thesis seeks to provide an
abstract framework to determine whether two lingusitically nuanced presenations
mean the same thing via their syntactic transformations. 

These syntactic transformations come in two flavors : parsing and
linearization, and are natively handled by a Logical Framework (LF) for
specifying grammars : Grammatical Framework (GF).

\begin{code}[hide]

module roadmap where

\end{code}

\begin{code}[hide]

{-# OPTIONS --cubical #-}

module Monoid where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude renaming (_∙_ to _∙''_)
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ : Level

is-left-unit-for : {A : Type ℓ} → A → (A → A → A) → Type ℓ
is-left-unit-for {A = A} e _⋆_ = (x : A) → e ⋆ x ≡ x

is-right-unit-for : {A : Type ℓ} → A → (A → A → A) → Type ℓ
is-right-unit-for {A = A} e _⋆_ = (x : A) → x ⋆ e ≡ x

is-assoc : {A : Type ℓ} → (A → A → A) → Type ℓ
is-assoc {A = A} _⋆_ = (x y z : A) → (x ⋆ y) ⋆ z ≡ x ⋆ (y ⋆ z)

record MonoidStrRec (A : Type ℓ) : Type ℓ where
  constructor
    monoid
  field
    ε   : A
    _∙_ : A → A → A

    left-unit  : is-left-unit-for ε _∙_
    right-unit : is-right-unit-for ε _∙_
    assoc      : is-assoc _∙_

    carrier-set : isSet A

record Monoid' : Type (ℓ-suc ℓ) where
  constructor
    monoid'
  field
    A : Type ℓ
    ε   : A
    _∙_ : A → A → A

    left-unit  : is-left-unit-for ε _∙_
    right-unit : is-right-unit-for ε _∙_
    assoc      : is-assoc _∙_

    carrier-set : isSet A

\end{code}

We now show yet another definition of a group homomorphism formalized in the
Agda programming language:

\begin{code}
monoidHom : {ℓ : Level} 
          → ((monoid' a _ _ _ _ _ _) (monoid' a' _ _ _ _ _ _) : Monoid' {ℓ} ) 
          → (a → a') → Type ℓ
monoidHom 
  (monoid' A ε _∙_ left-unit right-unit assoc carrier-set) 
  (monoid' A₁ ε₁ _∙₁_ left-unit₁ right-unit₁ assoc₁ carrier-set₁)
  f
  = (m1 m2 : A) → f (m1 ∙ m2) ≡ (f m1) ∙₁ (f m2)
\end{code}

While the first three definitions above are should be linguistically
comprehensible to a non-mathematician, this last definition is most certainly
not.  While may carry degree of comprehension to a programmer or mathematician
not exposed to Agda, it is certainly comprehensible to a computer : that is, it
typechecks on a computer where Cubical Agda is installed. While GF is designed
for multilingual syntactic transformations and is targeted for natural language
translation, it's underlying theory is largely based on ideas from the compiler
communities. A cousin of the BNF Converter (BNFC), GF is fully capable of
parsing progamming languages like Agda! And while the above definition is just
another concrete syntactic presentation of a group homomorphism, it is distinct
from the natural language presentations above in that the colors indicate it
has indeed type checked. 

While this example may not exemplify the power of Agda's type checker, it is of considerable 

Lorem ipsum~\cite{theunivalentfoundationsprogram-homotopytypetheory-2013}.

\begin{code}

open import Agda.Builtin.Sigma public

module Id where

data _≡_ {A : Set} (a : A) : A → Set where
  r : a ≡ a

infix 20 _≡_

J : {A : Set}
    → (D : (x y : A) → (x ≡ y) →  Set)
    -- → (d : (a : A) → (D a a r ))
    → ((a : A) → (D a a r ))
    → (x y : A)
    → (p : x ≡ y)
    ------------------------------------
    → D x y p
J D d x .x r = d x

\end{code}



\section{Goals and Challenges}


\section{Approach}

\bibliographystyle{plain}
\bibliography{references}

\end{document}
