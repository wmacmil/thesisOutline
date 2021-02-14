\documentclass{article}

\usepackage{fontspec}
\usepackage{fullpage}
\usepackage{hyperref}
\usepackage{agda}

\usepackage{unicode-math}

%\usepackage{amssymb,amsmath,amsthm,stmaryrd,mathrsfs,wasysym}

%\usepackage{enumitem,mathtools,xspace}
\usepackage{amsfonts}
\usepackage{mathtools}
\usepackage{xspace}


\usepackage{enumitem}


\setmainfont{DejaVu Serif}
\setsansfont{DejaVu Sans}
\setmonofont{DejaVu Sans Mono}

% \setmonofont{Fira Mono}
% \setsansfont{Noto Sans}

\usepackage{newunicodechar}

\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}

\newtheorem{definition}{Definition}
\newtheorem{lem}{Lemma}
\newtheorem{proof}{Proof}

\newcommand{\jdeq}{\equiv}      % An equality judgment
\newcommand{\refl}[1]{\ensuremath{\mathsf{refl}_{#1}}\xspace}
\newcommand{\define}[1]{\textbf{#1}}
\newcommand{\defeq}{\vcentcolon\equiv}  % A judgmental equality currently being defined

%\newcommand{\jdeq}{\equiv}      % An equality judgment
%\let\judgeq\jdeq


\newcommand{\ind}[1]{\mathsf{ind}_{#1}}
\newcommand{\indid}[1]{\ind{=_{#1}}} % (Martin-Lof) path induction principle for identity types

\newcommand{\blank}{\mathord{\hspace{1pt}\text{--}\hspace{1pt}}}

\newcommand{\opp}[1]{\mathord{{#1}^{-1}}}
\let\rev\opp

\newcommand{\id}[3][]{\ensuremath{#2 =_{#1} #3}\xspace}



\newcommand{\UU}{\ensuremath{\mathcal{U}}\xspace}
\let\bbU\UU
\let\type\UU






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

If one want to distill the meaning of each of these presentations, there is a
significant amount of subliminal interpretation happening very much analagous
to our innate lingusitic ussage.  The inverse and identity are discarded, even
though they are necessary data when defning a group. The order of presentation
of information is incostent, as well as the choice to use symbolic or natural
language information. In (3), the group operation is used implicitly, and its
clarification a side remark.

Details aside, these all mean the same thing--don't they?  This thesis seeks to provide an
abstract framework to determine whether two lingusitically nuanced presenations
mean the same thing via their syntactic transformations. 

These syntactic transformations come in two flavors : parsing and
linearization, and are natively handled by a Logical Framework (LF) for
specifying grammars : Grammatical Framework (GF).

\begin{code}[hide]
{-# OPTIONS --cubical #-}

module roadmap where

\end{code}

\begin{code}[hide]

module Monoid where

module Namespace1 where

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

[TODO: replace monoidhom with grouphom]

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

While this example may not exemplify the power of Agda's type checker, it is of
considerable interest to many. The typechecker has merely assured us that
monoidHom, is a well-formed type.  The type-checker is much more useful than is
immediately evident: it delegates the work of verifying that a proof is
correct, that is, the work of judging whether a term has a type, to the
computer. While it's of practical concern is immediate to any exploited grad
student grading papers late on a Sunday night, its theoretical concern has led
to many recent developments in modern mathematics. Thomas Hales solution to the
Kepler Conjecture was seen as unverifiable by those reviewing it. This led to
Hales outsourcing the verification to Interactive Theorem provers HOL Light and
Isabelle, during which led to many minor corrections in the original proof
which were never spotted due to human oversight.

Fields Medalist Vladimir Voevodsky, had the experience of being told one day
his proof of the Milnor conjecture was fatally flawed. Although the leak in the
proof was patched, this experience of temporarily believing much of his life's
work invalid led him to investigate proof assintants as a tool for future
thought. Indeed, this proof verification error was a key event that led to the
Univalent Foundations
Project~\cite{theunivalentfoundationsprogram-homotopytypetheory-2013}.

While Agda and other programming languages are capable of encoding definitions,
theorems, and proofs, they have so far seen little adoption, and in some cases
treated with suspicion and scorn by many mathematicians.  This isn't entirely
unfounded : it's a lot of work to learn how to use Agda or Coq, software
updates may cause proofs to break, and the inevitable errors we humans are
instilled in these Theorem Provers. And that's not to mention that Martin-Löf
Type Theory, the constructive foundational project which underlies these proof
assistants, is rejected by those who dogmatically accept the law of the
excluded middle and ZFC as the word of God.

It should be noted, the constructivist rejects neither the law of the excluded
middle nor ZFC. She merely observes them, and admits their handiness in certain
cituations. Excluded middle is indeed a helpful tool, as many mathematicians
may attest. The contention is that it should be avoided whenever possible -
proofs which don't rely on it, or it's corallary of proof by contradction, are
much more ameanable to formalization in systems with decideable type checking.
And ZFC, while serving the mathematicians of the early 20th century, is 
lacking when it comes to the higher dimensional structure of n-categories and
infinity groupoids.

What these theorem provers give the mathematician is confidence that her work
is correct, and even more importantly, that the work which she takes for
granted and references in her work is also correct. The task before us is then
one of religious conversion. And one doesn't undertake a conversion by simply
by preaching. Foundational details aside, this thesis is meant to provide a
blueprint for the syntactic reformation that must take place.  

It doesn't ask the mathematician to relinquish the beautiful language she has
come to love in expressing her ideas.  Rather, it asks her to make a compromise
for the time being, and use a Controlled Natural Language (CNL) to develop her
work. In exchange she'll get the confidence that Agda provides. Not only that,
she'll be able to search through a library, to see who else has possibly
already postulated and proved her conjecture. A version of this grandiose vision is 
explored in The Formal Abstracts Project.

\section{Preliminaries}

[Todo : Give overview of tools and theory in the making of this thesis]

\subsection{Grammatical Framework}

...

\subsection{Martin-Löf Type Theory}

...

\subsection{Agda}

...

\subsection{Natural Language and Mathematics}

...

\section{HoTT Proofs}

\subsection{Why HoTT for natural language?}

We note that all natural language definitions, theorems, and proofs are copied
here verbatim from the HoTT book.  This decision is admittedly arbitrary, but
does have some benefits.  We list some here : 

\begin{itemize}[noitemsep]

\item As the HoTT book was a collaborative effort, it mixes the language of
many individuals and editors, and can be seen as more ``linguistically
neutral''

\item By its very nature HoTT is interdiscplinary, conceived and constructed by
mathematicians, logicians, and computer scientists. It therefore is meant to
interface with all these discplines, and much of the book was indeed formalized
before it was written

\item It has become canonical reference in the field, and therefore benefits
from wide familiarity

\item It is open source, with publically available Latex files free for
modification and distribution

\end{itemize}

The genisis of higher type theory is a somewhat elementary observation : that
the identity type, parameterized by an arbitrary type $A$ and indexed by
elements of $A$, can actually be built iteratively from previous identities.
That is, $A$ may actually already be an identity defined over another type
$A'$, namely $A \defeq x=_{A'} y$ where $x,y:A'$. The key idea is that this
iterating identities admits a homotpical interpretation : 

\begin{itemize}[noitemsep]

\item Types are topological spaces
\item Terms are points in these space

\item Equality types $x=_{A} y$ are paths in $A$ with endpoints $x$ and $y$ in
$A$

\item Iterated equality types are paths between paths, or continuous path
deformations in some higher path space. This is, intuitively, what
mathematicians call a homotopy.

\end{itemize}

To be explicit, given a type $A$, we can form the homotopy $p=_{x=_{A} y}q$
with endpoints $p$ and $q$ inhabiting the path space $x=_{A} y$.

Let's start out by examining the inductive definition of the identity type.  We
present this definition as it appears in section 1.12 of the HoTT book.

\begin{definition}
  The formation rule says that given a type $A:\UU$ and two elements $a,b:A$, we can form the type $(\id[A]{a}{b}):\UU$ in the same universe.
  The basic way to construct an element of $\id{a}{b}$ is to know that $a$ and $b$ are the same.
  Thus, the introduction rule is a dependent function
  \[\refl{} : \prod_{a:A} (\id[A]{a}{a}) \]
  called \define{reflexivity},
  which says that every element of $A$ is equal to itself (in a specified way).  We regard $\refl{a}$ as being the
  constant path %path\indexdef{path!constant}\indexsee{loop!constant}{path, constant}
  at the point $a$.
\end{definition}

We recapitulate this definition in Agda, and treat : 

\begin{code}[hide]

module Id where

\end{code}
\begin{code}

  data _≡'_ {A : Set} : (a b : A) → Set where
    r : (a : A) → a ≡' a

\end{code}

\subsection{An introduction to equality}

There is already some tension brewing : most mathematicains have an intuition
for equality, that of an identitfication between two pieces of information
which intuitively must be the same thing, i.e. $2+2=4$. They might ask, what
does it mean to ``construct an element of $\id{a}{b}$''? For the mathematician
use to thinking in terms of sets $\{\id{a}{b} \mid a,b \in \mathbb{N} \}$ isn't
a well-defined notion. Due to its use of the axiom of extensionality, the set
theoretic notion of equality is, no suprise, extensional.  This means that sets
are identified when they have the same elements, and equality is therefore
external to the notion of set. To inhabit a type means to provide evidence for
that inhabitation. The reflexivity constructor is therefore a means of
providing evidence of an equality. This evidence approach is disctinctly
constructive, and a big reason why classical and constructive mathematics,
especially when treated in an intuitionistic type theory suitable for a
programming language implementation, are such different beasts.

In Martin-Löf Type Theory, there are two fundamental notions of equality,
propositional and definitional.  While propositional equality is inductively
defined (as above) as a type which may have possibly more than one inhabitant,
definitional equality, denoted $-\equiv -$ and perhaps more aptly named
computational equality, is familiarly what most people think of as equality.
Namely, two terms which compute to the same canonical form are computationally
equal. In intensional type theory, propositional equality is a weaker notion
than computational equality : all propositionally equal terms are
computationally equal. However, computational equality does not imply
propistional equality - if it does, then one enters into the space of
extensional type theory. 

Prior to the homotopical interpretation of identity types, debates about
extensional and intensional type theories centred around two features or bugs :
extensional type theory sacrificed decideable type checking, while intensional
type theories required extra beauracracy when dealing with equality in proofs.
One approach in intensional type theories treated types as setoids, therefore
leading to so-called ``Setoid Hell''. These debates reflected Martin-Löf's
flip-flopping on the issue. His seminal 1979 Constructive Mathematics and
Computer Programming, which took an extensional view, was soon betrayed by
lectures he gave soon thereafter in Padova in 1980.  Martin-Löf was a born
again intensional type theorist.  These Padova lectures were later published in
the "Bibliopolis Book", and went on to inspire the European (and Gothenburg in
particular) approach to implementing proof assitants, whereas the
extensionalists were primarily eminating from Robert Constable's group at
Cornell. 

This tension has now been at least partially resolved, or at the very least
clarified, by an insight Voevodsky was apparently most proud of : the
introduction of h-levels. We'll delegate these details for a later section, it
is mentioned here to indicate that extensional type theory was really ``set
theory'' in disguise, in that it collapses the higher path structure of
identity types. The work over the past 10 years has elucidated the intensional
and extensional positions. HoTT, by allowing higher paths, is unashamedly
intentional, and admits a collapse into the extensional universe if so desired.
We now the examine the structure induced by this propositional equality.

\subsection{All about Identity}

We start with a slight reformulation of the identity type, where the element
determining the equality is treated as a parameter rather than an index. This
is a matter of convenience more than taste, as it delegates work for Agda's
typechecker that the programmer may find a distraction. The reflexivity terms
can generally have their endpoints inferred, and therefore cuts down on the
beauracry which often obscures code. 

\begin{code}

  data _≡_ {A : Set} (a : A) : A → Set where
    r : a ≡ a

  infix 20 _≡_

\end{code}

It is of particular concern in this thesis, because it hightlights a
fundamental difference between the lingusitic and the formal approach to proof
presentation.  While the mathematician can whimsically choose to include the
reflexivity arguement or ignore it if she believes it can be inferred, the
programmer can't afford such a laxidasical attitude. Once the type has been
defined, the arguement strcuture is fixed, all future references to the
definition carefully adhere to its specification. The advantage that the
programmer does gain however, that of Agda's powerful inferential abilities,
allows for the insides to be seen via interaction windown. 

Perhaps not of much interest up front, this is incredibly important detail
which the mathematician never has to deal with explicity, but can easily make
type and term translation infeasible due to the fast and loose nature of the
mathematician's writing. Conversely, it may make Natural Language Generation
(NLG) incredibly clunky, adhering to strict rules when created sentences out of
programs. 

[ToDo, give a GF example]

A prime source of beauty in constructive mathematics arises from Gentzen's
recognition of a natural duality in the rules for introducing and using logical
connectives. The mutually coherence between introduction and elmination rules
form the basis of what has since been labeled harmony in a deductive system.
This harmony isn't just an artifact of beauty, it forms the basis for cuts in
proof normalization, and correspondingly, evaluation of terms in a programming
langauge. 

The idea is simple, each new connective, or type former, needs a means of
constructing its terms from its constiutuent parts, yielding introduction
rules. This however, isn't enough - we need a way of dissecting and using the
terms we construct. This yields an elimantion rule which can be uniquely
derived from an inductively defined type. These elimination forms yield
induction principles, or a general notion of proof by induction, when given an
interpration in mathematics. In the non-depedent case, this is known as a
recursion principle, and corresponds to recursion known by programmers far and
wide.  The proof by induction over natural numbers familiar to mathematicians
is just one special case of this induction principle at work--the power of
induction has been recognized and brought to the fore by computer scientists.

We now elaborate the most important induction principle in HoTT, namely, the
induction of an identity type.

\begin{definition}[Version 1]

Moreover, one of the amazing things about homotopy type theory is that all of the basic constructions and axioms---all of the
higher groupoid structure---arises automatically from the induction
principle for identity types.
Recall from [section 1.12]  that this says that if % \cref{sec:identity-types}
  \begin{itemize}[noitemsep]
    \item for every $x,y:A$ and every $p:\id[A]xy$ we have a type $D(x,y,p)$, and
    \item for every $a:A$ we have an element $d(a):D(a,a,\refl a)$,
  \end{itemize}
then
  \begin{itemize}[noitemsep]
    \item there exists an element $\indid{A}(D,d,x,y,p):D(x,y,p)$ for \emph{every}
    two elements $x,y:A$ and $p:\id[A]xy$, such that $\indid{A}(D,d,a,a,\refl a)
    \jdeq d(a)$.
  \end{itemize}
\end{definition}
The book then reiterates this definition, with basically no natural language,
essentially in the raw logical framework devoid of anything but dependent
function types.
\begin{definition}[Version 2]
In other words, given dependent functions
\begin{align*}
  D & :\prod_{(x,y:A)}(x= y) \; \to \; \type\\
  d & :\prod_{a:A} D(a,a,\refl{a})
\end{align*}
there is a dependent function
\[\indid{A}(D,d):\prod_{(x,y:A)}\prod_{(p:\id{x}{y})} D(x,y,p)\]
such that
\begin{equation}\label{eq:Jconv}
\indid{A}(D,d,a,a,\refl{a})\jdeq d(a)
\end{equation}
for every $a:A$.
Usually, every time we apply this induction rule we will either not care about the specific function being defined, or we will immediately give it a different name.

\end{definition}
Again, we define this, in Agda, staying as true to the syntax as possible.
\begin{code}

  J : {A : Set}
      → (D : (x y : A) → (x ≡ y) →  Set)
      → ((a : A) → (D a a r )) -- → (d : (a : A) → (D a a r ))
      → (x y : A)
      → (p : x ≡ y)
      ------------------------------------
      → D x y p
  J D d x .x r = d x

\end{code}

It should be noted that, for instance, we can choose to leave out the $d$ label
on the third line. Indeed minimizing the amount of dependent typing and using
vanilla function types when dependency is not necessary, is generally
considered ``best practice'' Agda, because it will get desugared by the time it
typechecks anyways. For the writer of the text; however, it was convenient to
define $d$ once, as there are not the same constraints on a mathematician
writing in latex. It will again, serve as a nontrivial exercise to deal with
when specifying the grammar, and will be dealt with later [ToDo add section].
It is also of note that we choose to include Martin-Löf's original name $J$, as
this is more common in the computer science literature.

Once the identity type has been defined, it is natural to develop an ``equality
calculus'',  so that we can actually use it in proof's, as well as develop the
higher groupoid structure of types. The first fact, that propositional equality
is an equivalence relation, is well motivated by needs of practical theorem
proving in Agda and the more homotopically minded mathematician. First, we show the symmetry of equality--that paths are reversible.

\begin{lem}\label{lem:opp}
  For every type $A$ and every $x,y:A$ there is a function
  \begin{equation*}
    (x= y)\to(y= x)
  \end{equation*}
  denoted $p\mapsto \opp{p}$, such that $\opp{\refl{x}}\jdeq\refl{x}$ for each $x:A$.
  We call $\opp{p}$ the \define{inverse} of $p$.
  %\indexdef{path!inverse}%
  %\indexdef{inverse!of path}%
  %\index{equality!symmetry of}%a
  %\index{symmetry!of equality}%
\end{lem}

\begin{proof}[First proof]
  Assume given $A:\UU$, and
  let $D:{\textstyle\prod_{(x,y:A)}}(x= y) \; \to \; \type$ be the type family defined by $D(x,y,p)\defeq (y= x)$.
  %$\prod_{(x:A)} \prod_{y:B}$
  In other words, $D$ is a function assigning to any $x,y:A$ and $p:x=y$ a type, namely the type $y=x$.
  Then we have an element
  \begin{equation*}
    d\defeq \lambda x.\ \refl{x}:\prod_{x:A} D(x,x,\refl{x}).
  \end{equation*}
  Thus, the induction principle for identity types gives us an element
  $\indid{A}(D,d,x,y,p): (y= x)$
  for each $p:(x= y)$.
  We can now define the desired function $\opp{(\blank)}$ to be 
  $\lambda p.\ \indid{A}(D,d,x,y,p)$, 
  i.e.\ we set 
  $\opp{p} \defeq \indid{A}(D,d,x,y,p)$.
  The conversion rule [missing reference] %rule~\eqref{eq:Jconv} 
  gives $\opp{\refl{x}}\jdeq \refl{x}$, as required.
\end{proof}
The Agda code is certainly more brief: 
\begin{code}

  _⁻¹ : {A : Set} {x y : A} → x ≡ y → y ≡ x
  _⁻¹ {A} {x} {y} p = J D d x y p
    where
      D : (x y : A) → x ≡ y → Set
      D x y p = y ≡ x
      d : (a : A) → D a a r
      d a = r

  infixr 50 _⁻¹

\end{code}

While first encountering induction principles can be scary, they are actually
more mechanical than one may think. This is due to the the fact that they
uniquely compliment the introduction rules of an an inductive type, and are
simply a means of showing one can ``map out'', or derive an arbitrary type
dependent on the type which has been inductively defined. The mechanical nature
is what allows for Coq's induction tactic, and perhaps even more elegantly,
Agda's pattern matching capabilities. It is always easier to use pattern
matching for the novice Agda programmer, which almost feels like magic.
Nonetheless, for completeness sake, the book uses the induction principle for
much of Chapter 2. And pattern matching is unique to programming languages,
its elegance isn't matched in the mathematicians' lexicon.

Here is the same proof via ``natural language pattern matching'' and Agda
pattern matching:

\begin{proof}[Second proof]
  We want to construct, for each $x,y:A$ and $p:x=y$, an element $\opp{p}:y=x$.
  By induction, it suffices to do this in the case when $y$ is $x$ and $p$ is $\refl{x}$.
  But in this case, the type $x=y$ of $p$ and the type $y=x$ in which we are trying to construct $\opp{p}$ are both simply $x=x$.
  Thus, in the ``reflexivity case'', we can define $\opp{\refl{x}}$ to be simply $\refl{x}$.
  The general case then follows by the induction principle, and the conversion rule $\opp{\refl{x}}\jdeq\refl{x}$ is precisely the proof in the reflexivity case that we gave.
\end{proof}

\begin{code}

  _⁻¹' : {A : Set} {x y : A} → x ≡ y → y ≡ x
  _⁻¹' {A} {x} {y} r = r

\end{code}

Next is trasitivity--concatenation of paths--and we omit the natural language
presentation, which is a slightly more sophisticated arguement than for
symmetry.  


\begin{code}
  _∙_ : {A : Set} → {x y : A} → (p : x ≡ y) → {z : A} → (q : y ≡ z) → x ≡ z
  _∙_ {A} {x} {y} p {z} q = J D d x y p z q
      where
      D : (x₁ y₁ : A) → x₁ ≡ y₁ → Set
      D x y p = (z : A) → (q : y ≡ z) → x ≡ z
      d : (z₁ : A) → D z₁ z₁ r
      d = λ v z q → q

  infixl 40 _∙_
\end{code}

Putting on our spectacles, the reflexivity term serves as evidence of a
constant path for any given point of any given type. To the category theorist,
this makes up the data of an identity map. Likewise, conctanation of paths
starts to look like function composition. This, along with the identity laws
and associativity as proven below, gives us the data of a category. And we have
not only have a category, but the symmetry allows us to prove all paths are
isomorphisms, giving us a groupoid. This isn't a coincedence, it's a very deep
and fascinating articulation of power of the machinery we've so far built. The
fact the path space over a type naturally must satisfies coherence laws in an
even higher path space gives leads to this notion of types as higher groupoids.  

As regards the natural language--at this point, the bookkeeping starts to get hairy.  Paths between paths, and paths between paths between paths, these ideas start to lose geometric inutiotion. And the mathematician, while they write 

Many of the proofs beyond this point are either routinely made via
the induction principle, or even more routinely by just pattern matching on
equality paths, we omit the details which can be found in the HoTT book, but it
is expected that the GF parser will soon cover such examples.

\begin{code}
  iₗ : {A : Set} {x y : A} (p : x ≡ y) → p ≡ r ∙ p
  iₗ {A} {x} {y} p = J D d x y p 
    where
      D : (x y : A) → x ≡ y → Set
      D x y p = p ≡ r ∙ p
      d : (a : A) → D a a r
      d a = r

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

\end{code}


\section{Goals and Challenges}

\bibliographystyle{plain}
\bibliography{references}

\end{document}
