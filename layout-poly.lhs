% -*- LaTeX -*-

\documentclass[10pt,sigplan,screen,dvipsnames,nonacm]{acmart}
\settopmatter{printacmref=false,printfolios=true}

\usepackage{supertabular}

\input{ott}

%% lhs2TeX gubbins
%include ocaml.fmt

\renewcommand{\ottkw}[1]{\keyword{#1}}
\renewcommand{\ottgrammartabular}[1]{\begin{supertabular}{@@{}l@@{}lcl@@{}l@@{}llll}#1\end{supertabular}}
\renewcommand{\ottusedrule}[1]{\[#1\]\\}

\setcopyright{none}

\title{Layout Polymorphism}
\subtitle{Using static computation to allow efficient polymorphism over variable representations}

\author{Richard A.~Eisenberg}
\affiliation{
  \institution{Jane Street}
  \city{New York}
  \country{USA}
}
\email{reisenberg@@janestreet.com}

\begin{document}

\begin{abstract}
  %% Despite the great success achieved by garbage collected languages,
  %% pausing a program in order to sweep up its garbage introduces
  %% latency.
  In a small subset of the OCaml programs in use at Jane
  Street, the unpredictable latency induced by garbage collection is problematic.
  %% To reduce the
  %% need for garbage collection and to avoid this latency,
  We are thus in the
  process of designing and implementing unboxed types for OCaml. These
  unboxed types can be created and manipulated without the need for
  allocation or the production of garbage.

  However, all is not well. Heap-allocated types (along with |int|)
  have a uniform representation, enabling polymorphic
  functions to work over any type even while the types themselves
  are erased. On the other hand, unboxed types come in a wide array
  of representations, thwarting parametric polymorphism. We dub the
  representation of an unboxed type its \emph{layout}. This proposal
  describes an approach to \emph{layout polymorphism}, allowing a
  function to work over a variety of representations. The underlying
  mechanism essentially echoes C++-style templates, requiring layout-polymorphic
  functions to be specialized at compile time. The innovation, however,
  is in continuing ML's tradition of \emph{abstraction}: in contrast to C++, we wish to
  type-check the layout-polymorphic functions \emph{before} specializing,
  guaranteeing that the specialized version will run successfully.

  The talk will describe our approach, including both type-system
  design (including a novel \emph{static mode}) and implementation
  concerns around managing generating the specializations without
  interfering with separate compilation.
\end{abstract}

\maketitle

\section{Introduction}

Many high-level language runtimes come equipped with
a garbage collector, freeing the programmer from the need
to worry about memory deallocation. This freedom has paid
large dividends, allowing us to design languages that put
immutability first and thus more closely
mimic mathematical expression. OCaml embodies this advantage,
and Jane Street owes its success in part to OCaml's ability
to operate at a high level.

Yet despite the advantage that a garbage collector (GC) brings,
it has a cost: when enough garbage has accumulated, the program
must pause while the GC operates. For most programs, this small
interruption is not noticeable and causes no trouble. However,
for a small minority of the OCaml programs in use at Jane Street,
the unpredictable latency induced by the GC is problematic.

Accordingly, we seek a way to avoid allocation, to be used in these
few programs where GC latency causes real pain. A natural way
to achieve this goal is to use \emph{unboxed types}: types whose
values can
be placed on the call stack or directly in registers, avoiding heap
allocation. Many other languages support such types, called value types in \href{https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/builtin-types/value-types}{C\#} and (proposed) \href{https://openjdk.org/jeps/8277163}{Java}, or called unboxed types in Haskell~\cite{levity-polymorphism}.
In C, C++, and \href{https://doc.rust-lang.org/rust-by-example/std/box.html}{Rust}, |struct|s are unboxed by default but may optionally
be boxed and placed on the heap.

A key challenge in working with unboxed types is that their representation
is \emph{non-uniform}. Boxed types, allocated on the heap, all have a
uniform representation: a pointer to the allocated memory. In OCaml, the
type |int|, despite not requiring a box, shares this representation, as
it fits in a machine word. Unboxed types come in all shapes and sizes, however:
generally each unboxed type has its own unique representation.\footnote{I say ``generally''
here because an abstract type represented by, say, an unboxed |float| will share
the representation of the underlying representation. Similarly, unboxed records
with the same components will share representations.} This poses a major
problem for polymorphism: we wish to retain type erasure, and so how can
a function polymorphically manipulate values when those values might have
an unknown representation?

This extended abstract presents our work-in-progress approach toward a solution to this
challenge. In our ongoing work designing and implementing unboxed types,
we have called the memory and register representation of an unboxed
type to be its \emph{layout}. Thus, we seek to allow \emph{layout polymorphism}.
Here is an example:

\begin{code}
module Float_u : sig
  sqrt : #float -> #float
end = ...

type point = { x : int; y : int }
let x10 (group(hash { x; y })) = #{ x = x * 10; y = y * 10 }

let twice : (alpha : any). (alpha -> alpha) -> alpha -> alpha =
  fun f x -> f (f x)
let two : #float = twice Float_u.sqrt (group(hash 16.0))
let hundreds : #point = twice x10 (group(hash { x = #1.0; y = #1.0 })
\end{code}

In this example, |#float| is the type of unboxed floating point numbers,
and the type |#point| is the unboxed version of the ordinary record type
|point|. The |twice| function works with the type variable |alpha|, declared
to have |any| layout. We then see in the last two lines that the polymorphic function
|twice| is called on arguments with two different representations:
unboxed floats (stored in a floating-point register), and unboxed points
(stored in two general-purpose registers).

The main mechanism by which this works is through \emph{specialization}.
That is, when a programmer wishes to use a layout-polymorphic function,
the compiler creates a specialized version of the function, which works
with the specific representation of the argument(s) at hand. This design
echoes the design of C++ templates, which are similarly specialized.
We deviate from C++, however, in that we retain full \emph{abstraction},
as dictated by OCaml's rich module system. A C++ template need not be type-checked
at declaration time; instead, it is checked afresh at every specialization.
This requires the full definition of the templated function to be available
at every usage site, confounding both separate compilation and abstraction.
The rest of this talk proposal addresses our current thinking about
the solutions to these two problems; however, this is all work in progress
and may evolve between now and the presentation at the workshop.\footnote{This material
is appropriate for either the ML Workshop or the OCaml Workshop. I have decided
to submit to the ML Workshop, given that the challenges inherent in our approach
would apply to any ML-family language -- and many beyond. However, I would be
happy also to present at the OCaml Workshop.}

\section{Abstraction}

The first challenge in layout polymorphism is figuring out how this feature
works with the module system. The key criterion is that, when we see a function
call |f x|, if |f| is layout-polymorphic, we must be able to resolve |f| to a
specific function definition at compile-time. We do \emph{not} need to have
|f|'s definition loaded, but we do need to know, say, what file |f| was defined
in. This, in turn, allows a build system to produce the specialization of
|f| at the appropriate layout. In addition to being able to resolve |f| to a
definition site, we also must know the layouts at which to specialize. This
second challenge is easier, so let's address it first.

\subsection{Specialization}

When we see |twice Float_u.sqrt #16.0|, we need to know that the type
variable |alpha| in |twice|'s type should be specialized to layout
|float64| (the layout of |#float|). Our approach here is to imagine
translating |twice|'s type |(alpha : any). (alpha -> alpha) -> alpha
-> alpha| to use explicit layout quantification: |(xi : layout) (alpha
: xi). (alpha -> alpha) -> alpha -> alpha|.  Here, |xi| is a
\emph{layout variable}, distinguished by the hypothetical syntax
$\mathrel{:} |layout|$. When applying |twice Float_u.sqrt|, we infer
that |xi| is instantiated with |float64|, and then can substitute
|float64| for |xi| in the rest of the function, creating a function of
type |(alpha : float64). (alpha -> alpha) -> alpha -> alpha|, which can
easily be compiled.

We choose not to expose layout variables to the user---instead, preferring
using the |(alpha : any)| syntax---for simplicity. This is in contrast
to Haskell, where their equivalent of layout polymorphism~\cite{levity-polymorphism} must be written
by users.

\subsection{Static resolution}

As explained above, in a layout-polymorphic function call |f x|, we must be
able to find |f|'s definition site at compile-time. Before diving into our
approach, let's first see why this might be hard. The most obvious challenge
would be if a function argument were layout-polymorphic; however, this is
easy to prevent, as OCaml does not support higher-rank polymorphism, and so
we already get this protection.\footnote{\citet{polymorphic-parameters} introduces
higher-rank polymorphism, but it is easy to restrict this to work only
in layout-monomorphic situations.} However, even lacking higher-rank polymorphism,
we can run into trouble:

\begin{code}
module type CHOICE = sig
  choose : (alpha : any). alpha -> alpha -> alpha
end

module Choose_first : CHOICE = struct
  choose : (alpha : any). alpha -> alpha -> alpha = fun x _ -> x
end

module Choose_second : CHOICE = struct
  choose : (alpha : any). alpha -> alpha -> alpha = fun _ y -> y
end

let which_one =
  let (module C) =
    if flip_coin ()
    then (module Choose_first : CHOICE)
    else (module Choose_second : CHOICE)
  in
  C.choose (group (hash 1.0)) (group (hash 2.0))
\end{code}

There is no way to tell, at compile time, which |choose| will be chosen.

In order to prevent a program such as this one, we introduce a \emph{static mode}.
An expression well-typed at the static mode can be reduced to a value at compile
time. The function in a layout-polymorphic function application must be well-typed
at the static mode, and thus we can be assured that its definition can be resolved
at compile time. The static mode admits most constructs in the OCaml language,
but nothing with side effects, such as |flip_coin|. The broad strokes of the static
mode are unsurprising, but the devil is in the details. See the appendix of this
proposal for our current draft type system containing the static mode; in that
presentation, we choose the |if| construct as the operation that can be performed
only at runtime, though our implementation may allow static computation of |if|
if the condition is known statically.

\section{Separate compilation}

When compiling a layout-polymorphic function call |f x|, even if we can resolve
|f| to a specific definition site at compile time, we might not have access to
the actual function body of |f|. This is good: it is part of OCaml's abstraction
guarantee, where only the type of |f| is exported, not its implementation details.
This design is reified in the requirements of the @ocamlc@ compiler: an @.ml@ file
depends on other @.mli@ files, but not on other @.ml@ files; @.ml@ files can
be compiled in any order, as long as all dependent @.mli@ files are available.

Accordingly, we must be able to specialize the function |f| without knowing
its definition. Our implementation plan here is to leverage the build system.
That is, suppose |f| is defined in @fmod.ml@ and the call to |f| is in @usemod.ml@.
That call in @usemod.ml@ specializes |f| to operate at layout |float64|. The
compiled code in @usemod.cmo@ will include a call to a mangled name such as
@fmod_f_float64@, and the compiler will also output a listing of the specializations
it needs. The build system will then consult this list, registering the specializations
as dependencies of the final, linked program. To build these dependencies, the build
system would then return to @fmod.cmo@ (which would contain the implementation of |f|)
and specialize it, producing a version with the correct, mangled name. This would
then get linked into the final program.

The approach sketched here indeed places new demands on the build system, but
they are demands the build system is well suited for: registering and resolving
dependencies, and avoiding duplication if, say, @usemod2.ml@ also needs |f|
specialized to |float64|.

A small complication is that we might want to go further than just specialization:
we might wish to \emph{inline} |f| at its usage site, as inlining might be
an effective optimization. Inlining, here as ever, requires knowing the definition
of |f| when compiling its usage sites, so layout polymorphism does not significantly
complicate this picture.

We at Jane Street are concerned about code bloat from the approach described here:
if we need to make lots of specializations of lots of functions, might our executables
become too big? While this is indeed a possibility, we still wish to explore this
angle of attack to see if it really becomes a problem in practice. After all, it seems
impossible to both get efficient compilation of layout-polymorphic programs and
avoid this bloat.

\section{Conclusion}

Layout polymorphism---as just one part of the larger unboxed types initiative---is a
key challenge to face down in the coming months. Yet we think working in the language
with unboxed types but without layout polymorphism would be too painful, and that the
solutions imagined here---especially the static mode with its ability to flag work
that can be done ahead of runtime---may prove handy beyond this one motivating use-case.

\begin{acks}
This is joint work with my Jane Street colleagues. Chief contributors to the ideas here
include Leo White, Luke Maurer, and Chris Casinghino.
\end{acks}

\bibliographystyle{ACM-Reference-Format}
\bibliography{rae}

\appendix

\section*{Appendix}

These rules are a capture of our thinking at this point in time. They will likely
evolve as we continue to work out the details. The key property we hope to prove
using this formalism is that a term well-typed at the static mode can be reduced
to a value without using any dynamic constructs. In the formalism as presented,
the only dynamic construct is |if|, included simply to have one such example
construct.

\ottgrammar\\[2ex]
\ottdefnss

\end{document}
