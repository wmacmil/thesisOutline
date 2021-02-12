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
that is normally ignored or taken for granted by the fluent mathematician. These all mean the same thing--don't they?  This thesis seeks to provide an abstract framework to determine whether two lingusitically nuanced presenations mean the same thing via their syntactic transformations. 

These syntactic transformations come in two flavors : parsing and
linearization, and are natively handled by a Logical Framework (LF) for
specifying grammars : Grammatical Framework (GF).


\begin{code}[hide]

{-# OPTIONS --cubical #-}

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

We now show yet another definition of a group homomorphism, 

\begin{code}
monoidHom : {ℓ : Level} → ((monoid' a _ _ _ _ _ _) (monoid' a' _ _ _ _ _ _) : Monoid' {ℓ} ) → (a → a') → Type ℓ
monoidHom (monoid' A ε _∙_ left-unit right-unit assoc carrier-set) (monoid' A₁ ε₁ _∙₁_ left-unit₁ right-unit₁ assoc₁ carrier-set₁) f = (m1 m2 : A) → f (m1 ∙ m2) ≡ (f m1) ∙₁ (f m2)
\end{code}

Lorem ipsum~\cite{theunivalentfoundationsprogram-homotopytypetheory-2013}.

\begin{code}
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
\end{code}

\section{Goals and Challenges}


\begin{code}

open import Agda.Builtin.Sigma public

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

_⁻¹ : {A : Set} {x y : A} → x ≡ y → y ≡ x
_⁻¹ {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = y ≡ x
    d : (a : A) → D a a r
    d a = r

infixr 50 _⁻¹

_∙_ : {A : Set} → {x y : A} → (p : x ≡ y) → {z : A} → (q : y ≡ z) → x ≡ z
_∙_ {A} {x} {y} p {z} q = J D d x y p z q
    where
    D : (x₁ y₁ : A) → x₁ ≡ y₁ → Set
    D x y p = (z : A) → (q : y ≡ z) → x ≡ z
    d : (z₁ : A) → D z₁ z₁ r
    d = λ v z q → q


infixl 40 _∙_

-- leftId : {A : Set} → (x y : A) → (p : I A x y) → I (I A x y) p (trans x x y r p)
iₗ : {A : Set} {x y : A} (p : x ≡ y) → p ≡ r ∙ p
iₗ {A} {x} {y} p = J D d x y p 
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p ≡ r ∙ p
    d : (a : A) → D a a r
    d a = r


-- similairlymeans uniformly substitute the commuted expression throughout the proof.  this applies to all of the proofs
iᵣ : {A : Set} {x y : A} (p : x ≡ y) → p ≡ p ∙ r
iᵣ {A} {x} {y} p = J D d x y p 
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p ≡ p ∙ r
    d : (a : A) → D a a r
    d a = r


leftInverse : {A : Set} {x y : A} (p : x ≡ y) → p ⁻¹ ∙ p ≡ r 
leftInverse {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p ⁻¹ ∙ p ≡ r
    d : (x : A) → D x x r
    d x = r

-- lI : {A : Set} {x y : A} (p : x ≡ y) → p ⁻¹ ∙ p ≡ r 
-- lI r = r

rightInverse : {A : Set} {x y : A} (p : x ≡ y) → p ∙ p ⁻¹ ≡ r 
rightInverse {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p ∙ p ⁻¹ ≡ r
    d : (a : A) → D a a r
    d a = r

doubleInv : {A : Set} {x y : A} (p : x ≡ y) → p ⁻¹ ⁻¹ ≡ p
doubleInv {A} {x} {y} p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = p ⁻¹ ⁻¹ ≡ p
    d : (a : A) → D a a r
    d a = r

associativity :{A : Set} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r' : z ≡ w ) → p ∙ (q ∙ r') ≡ p ∙ q ∙ r'
associativity {A} {x} {y} {z} {w} p q r' = J D₁ d₁ x y p z w q r'
  where
    D₁ : (x y : A) → x ≡ y → Set
    D₁ x y p = (z w : A) (q : y ≡ z) (r' : z ≡ w ) → p ∙ (q ∙ r') ≡ p ∙ q ∙ r'
    -- d₁ : (x : A) → D₁ x x r 
    -- d₁ x z w q r' = r -- why can it infer this 
    D₂ : (x z : A) → x ≡ z → Set
    D₂ x z q = (w : A) (r' : z ≡ w ) → r ∙ (q ∙ r') ≡ r ∙ q ∙ r'
    D₃ : (x w : A) → x ≡ w → Set
    D₃ x w r' =  r ∙ (r ∙ r') ≡ r ∙ r ∙ r'
    d₃ : (x : A) → D₃ x x r
    d₃ x = r
    d₂ : (x : A) → D₂ x x r
    d₂ x w r' = J D₃ d₃ x w r' 
    d₁ : (x : A) → D₁ x x r
    d₁ x z w q r' = J D₂ d₂ x z q w r'

-- -- the then D₁(x,x,reflₓ) is ... actually shows up in the goal when we have the unfilled hole

-- whiskering
_∙ᵣ_ : {A : Set} → {b c : A} {a : A} {p q : a ≡ b} (α : p ≡ q) (r' : b ≡ c) → p ∙ r' ≡ q ∙ r'
_∙ᵣ_ {A} {b} {c} {a} {p} {q} α r' = J D d b c r' a α
  where
    D : (b c : A) → b ≡ c → Set
    D b c r' = (a : A) {p q : a ≡ b} (α : p ≡ q) → p ∙ r' ≡ q ∙ r'
    d : (a : A) → D a a r
    d a a' {p} {q} α = iᵣ p ⁻¹ ∙ α ∙ iᵣ q

-- iᵣ == ruₚ

_∙ₗ_ : {A : Set} → {a b : A} (q : a ≡ b) {c : A} {r' s : b ≡ c} (β : r' ≡ s) → q ∙ r' ≡ q ∙ s
_∙ₗ_ {A} {a} {b} q {c} {r'} {s} β = J D d a b q c β
  where
    D : (a b : A) → a ≡ b → Set
    D a b q = (c : A) {r' s : b ≡ c} (β : r' ≡ s) → q ∙ r' ≡ q ∙ s
    d : (a : A) → D a a r
    d a a' {r'} {s} β = iₗ r' ⁻¹ ∙ β ∙ iₗ s

_⋆_ : {A : Set} → {a b c : A} {p q : a ≡ b} {r' s : b ≡ c} (α : p ≡ q) (β : r' ≡ s) → p ∙ r' ≡ q ∙ s
_⋆_ {A} {q = q} {r' = r'} α β = (α ∙ᵣ r') ∙ (q ∙ₗ β)

_⋆'_ : {A : Set} → {a b c : A} {p q : a ≡ b} {r' s : b ≡ c} (α : p ≡ q) (β : r' ≡ s) → p ∙ r' ≡ q ∙ s
_⋆'_ {A} {p = p} {s = s} α β =  (p ∙ₗ β) ∙ (α ∙ᵣ s)

Ω : {A : Set} (a : A) → Set
Ω {A} a = a ≡ a

Ω² : {A : Set} (a : A) → Set
Ω² {A} a = _≡_ {a ≡ a} r r 

lem1 : {A : Set} → (a : A) → (α β : Ω² {A} a) → (α ⋆ β) ≡ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ∙ (iₗ r ⁻¹ ∙ β ∙ iₗ r)
lem1 a α β = r

lem1' : {A : Set} → (a : A) → (α β : Ω² {A} a) → (α ⋆' β) ≡  (iₗ r ⁻¹ ∙ β ∙ iₗ r) ∙ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r)
lem1' a α β = r

-- ap\_
apf : {A B : Set} → {x y : A} → (f : A → B) → (x ≡ y) → f x ≡ f y
apf {A} {B} {x} {y} f p = J D d x y p
  where
    D : (x y : A) → x ≡ y → Set
    D x y p = {f : A → B} → f x ≡ f y
    d : (x : A) → D x x r
    d = λ x → r 

ap : {A B : Set} → {x y : A} → (f : A → B) → (x ≡ y) → f x ≡ f y
ap f r = r

lem20 : {A : Set} → {a : A} → (α : Ω² {A} a) → (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ≡ α
lem20 α = iᵣ (α) ⁻¹

lem21 : {A : Set} → {a : A} → (β : Ω² {A} a) → (iₗ r ⁻¹ ∙ β ∙ iₗ r) ≡ β
lem21 β = iᵣ (β) ⁻¹

lem2 : {A : Set} → (a : A) → (α β : Ω² {A} a) → (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ∙ (iₗ r ⁻¹ ∙ β ∙ iₗ r) ≡ (α ∙ β)
lem2 {A} a α β = apf (λ - → - ∙ (iₗ r ⁻¹ ∙ β ∙ iₗ r) ) (lem20 α) ∙ apf (λ - → α ∙ -) (lem21 β)

lem2' : {A : Set} → (a : A) → (α β : Ω² {A} a) → (iₗ r ⁻¹ ∙ β ∙ iₗ r) ∙ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r) ≡ (β ∙ α )
lem2' {A} a α β =  apf  (λ - → - ∙ (iᵣ r ⁻¹ ∙ α ∙ iᵣ r)) (lem21 β) ∙ apf (λ - → β ∙ -) (lem20 α)
-- apf (λ - → - ∙ (iₗ r ⁻¹ ∙ β ∙ iₗ r) ) (lem20 α) ∙ apf (λ - → α ∙ -) (lem21 β)

⋆≡∙ : {A : Set} → (a : A) → (α β : Ω² {A} a) → (α ⋆ β) ≡ (α ∙ β)
⋆≡∙ a α β = lem1 a α β ∙ lem2 a α β

-- proven similairly to above 
⋆'≡∙ : {A : Set} → (a : A) → (α β : Ω² {A} a) → (α ⋆' β) ≡ (β ∙ α)
⋆'≡∙ a α β = lem1' a α β ∙ lem2' a α β

-- -- _⋆_ : {A : Set} → {a b c : A} {p q : a ≡ b} {r' s : b ≡ c} (α : p ≡ q) (β : r' ≡ s) → p ∙ r' ≡ q ∙ s
-- _⋆≡⋆'_ : {A : Set} → {a b c : A} {p q : a ≡ b} {r' s : b ≡ c} (α : p ≡ q) (β : r' ≡ s) → (α ⋆ β) ≡ (α ⋆' β)
-- _⋆≡⋆'_ {A} {a} {b} {c} {p} {q} {r'} {s} α β = J D d p q α c r' s β
--   where
--     D : (p q : a ≡ b) → p ≡ q → Set
--     D p q α = (c : A) (r' s : b ≡ c) (β : r' ≡ s) → (α ⋆ β) ≡ (α ⋆' β)
--     E : (r' s : b ≡ c) → r' ≡ s → Set
--     -- E p q β = (r ⋆ β) ≡ (r ⋆' β) 
--     E r' s β = (_⋆_ {A} {b = b} {c} {r} {r} {r' = r'} {s = s} r β) ≡ (r ⋆' β)
--     e : ((s : b ≡ c) → E s s r)
--     e r = r
--     d : ((p : a ≡ b) → D p p r)
--     d p c r' s β = {!J E e  !}
--     -- d r r .r r = r

    -- E : (r' s : a ≡ c) → r' ≡ s → Set
    -- E p q β = (_⋆_ {A} {a} {a} {c} {r} {r} {p} {q} r β) ≡ (r ⋆' β)
    -- e : ((pr : a ≡ c) → E pr pr r)
    -- e r = r
    -- d : (x : (a ≡ a)) → D x x r
    -- d = λ x → {!!}

-- _⋆_ : {A : Set} → {a b c : A} {p q : a ≡ b} {r' s : b ≡ c} (α : p ≡ q) (β : r' ≡ s) → p ∙ r' ≡ q ∙ s
-- _⋆_ {A} {q = q} {r' = r'} α β = (α ∙ᵣ r') ∙ (q ∙ₗ β)


--eckmannHilton : {A : Set} → (a : A) → (α β : Ω² {A} a) → α ∙ β ≡ β ∙ α 
--eckmannHilton a α β = {!!} 
--  where
--    l0 : (α ⋆ β) ≡ α ∙ β
--    l0 = ⋆≡∙ a α β
--    l0' : (α ⋆' β) ≡ β ∙ α
--    l0' = ⋆'≡∙ a α β
\end{code}

more text second citation~\cite{theunivalentfoundationsprogram-homotopytypetheory-2013}.

\begin{code}

data Tree (A : Set) : Set where
  Leaf : A -> Tree A
  Node : Tree A -> Tree A -> Tree A


\end{code}



\section{Approach}

\bibliographystyle{plain}
\bibliography{references}

\end{document}
