---
title: A Lattice of Languages is a Verification Buffet
tags: verification, types, semantics, linear-types, cdsl, total, functional, edsls, reasoning
preamble: \usepackage{amsmath}\usepackage{amsfonts}\usepackage[all]{xy}\usepackage[usenames,dvipsnames,svgnames,table]{xcolor}\usepackage{stmaryrd}
---

I have [written before](http://liamoc.net/posts/2013-11-13-imperativereasoning.html) about the use of total, purely functional languages to eliminate cumbersome low-level reasoning. By having a denotational semantics that are about as straightforward as highschool algebra,
we can make many verification problems substantially simpler. Totality and the absence of effects [^1] means that we can pick redexes in any order, and have a wellfounded induction principle for datatypes [@Turner]. 

In existing large-scale verified software artifacts like [seL4](http://sel4.systems) however, we still use _C_ as our implementation language[^2], despite the fact that it is positively hellish to reason about [@Koenig]. The reasons
for this are numerous, but there are two main ones. The first concern, and the least important, is that most purely functional language implementations, and certainly all total ones, depend on a runtime, which would
enlarge the [trusted computing base](http://en.wikipedia.org/wiki/Trusted_computing_base), and compromise the system's efficiency. The second and more pressing concern is that for low-level systems like microkernels, or even services such as drivers and file system
servers, are forced to confront the reality of the von Neumann architecture. Sometimes they might need to manipulate some bytes in memory, or perform potentially unsafe pointer arithmetic. If we are to follow
traditional systems orthodoxy, they simply cannot be efficiently expressed at the level of abstraction of say, Haskell.

This has meant that these systems are forced to choose an implementation language which requires no runtime support and which supports all of these unsafe features. Sadly, traditional "systems" languages
such as C, while satisfying this criteria, will always extract their pound of flesh when it comes to verification. The huge cost to verifiability that comes with allowing divergence and unsafe memory access
and so on is not just paid where those semantic features are used, but _everywhere in the program_. The majority of the seL4 proofs are concerned with re-establishing refinement invariants between
a state-monadic executable specification and the C implementation. This specification is semantically equivalent, more or less, to the C implementation, but the proof is huge. The majority of obligations
are about things like pointer validity, heap validity, type safety, loop termination and so on -- things that we don't have to worry about in total, pure languages. 

My research project is focused on reducing the cost of verification by replacing the systems implementation language with one that has a straightforward denotational semantics, about which
correctness properties can be easily stated. This language is under a number of constraints: It can't rely on a runtime, and it must have minimal performance overhead compared to a manually
written C implementation. Furthermore, the compilation needs to be highly trustworthy.

The language Cogent, which we will submit to POPL this year, is essentially a linear lambda calculus, with a bunch of usability features, such as pattern matching, records and a simple C FFI. The use of linear types
eliminates the need for a garbage collector, and allows for efficient implementation of a purely functional semantics using destructive updates [@Wadler]. Indeed, two semantics are ascribed to
the language: One which resembles any pure functional language (a denotation in terms of sets and total functions), and one which is of a much more imperative flavour (with a state monadic denotation).
We have proven that the imperative semantics is a refinement of the pure semantics for any well-typed program, and the compiler _co-generates_ an efficient C implementation and a proof,
in [Isabelle/HOL](http://isabelle.in.tum.de) [@Nipkow], that this imperative semantics is an abstraction of the C code it generates. 

To verify properties about programs written in this language, it suffices to use the simple equational reasoning tactics used for any HOL program. Hoare logic and stateful reasoning are gone, and high-level
properties are generally stated as equations between terms. The snag, however, is in the C FFI. As the language is so restrictive (total, safe, and with no indirectly observable mutation), the C
FFI is used heavily to provide everything from red-black trees to loop iterators. While Cogent lets us reason nicely about code written in it, the moment a C function is used it produces a number
of thorny proof obligations, essentially requiring us to show that, at least to an outside observer, the C code has not violated the invariants assumed by Cogent's type system.

We were able to express the vast majority of an Ext2 file system implementation in Cogent, and the verification of file systems written in Cogent is certainly easier than a raw C implementation. However,
there are a number of places in the file system implementation where efficiency is sacrificed in order to be able to express the file system in a safe way. For example, deserialising structures
from a disk buffer into file system structures is done byte-by-byte, rather than by a memory map.

The flaw in Cogent's approach is that it's all-or-nothing. If a program can't be expressed in this highly restrictive language, it must be expressed in C, and then all of Cogent's verification advantages
are lost.

To remedy this, I first designed a _spectrum_ of languages, each differing primarily in their treatment of memory.

$$
\xymatrix@R=0.1em{
& \mathcal{L}_C & \mathcal{L}_R & \mathcal{L}_\textbf{1} \\
\text{Liberty} & \ar[rrr] & \ar[ll]  & & \text{Safety} \\
}
$$

The language $\mathcal{L}_\textbf{1}$ is more or less Cogent as it exists now. Linear types allow for the extremely simple semantics that make verification much easier. The language $\mathcal{L}_R$ is less
restrictive, by doing away with linear types and bringing explicit references to the language. This introduces manual memory management, and stateful reasoning, however the memory model remains fairly
high level. It is possible to leak memory or invalidate pointers in $\mathcal{L}_R$, unlike $\mathcal{L}_\textbf{1}$, but the lack of linear types now permits programs that rely on sharing mutable
pointers, such as efficient data structure implementations. The lowest level language $\mathcal{L}_C$ is also stateful, but the state consists of a heap of bytes. Here, pointer arithmetic is permitted,
as well as arbitrary casting and reinterpretation of memory, more or less on the same semantic level as C.

Clearly, the compiler for $\mathcal{L}_\textbf{1}$ can simply compile to $\mathcal{L}_R$, and $\mathcal{L}_R$ to $\mathcal{L}_C$. Once in $\mathcal{L}_C$, it is straightforward to emit implementation code
in LLVM IR or C. The advantage of this spectrum is that we can allow the programmer access to _every_ level of abstraction. I plan to achieve this by allowing code from $\mathcal{L}_C$ to be written _inline_
inside $\mathcal{L}_R$, and both of these in turn inside $\mathcal{L}_\textbf{1}$, in the vein of the inline assembly language supported by most C compilers. The crucial point here is that each of these
inline blocks will generate a _proof obligation_ to ensure that, externally, the inline block is "well-behaved" with respect to the abstractions of the higher level language. For example, embedding
$\mathcal{L}_C$ inside $\mathcal{L}_R$ generates the obligation that any valid pointers left by the $\mathcal{L}_C$ program point to data of the right type. Embedding $\mathcal{L}_R$ inside $\mathcal{L}_\textbf{1}$
requires showing that all available pointers are valid, no memory was leaked, and that there is at most one pointer to each object remaining. I am exploring the possibility of making each of these
languages embedded inside a dependently-typed programming language such as Agda or Idris, to allow the proofs to be expressed along with the program.

These different languages are all total. Trying to fit recursion or loops into our spectrum leads to some unfortunate consequences. Putting them on the "Liberty" side would mean throwing away our
nice memory model whenever we want to write a loop, and putting it to the left of $\mathcal{L}_\textbf{1}$ on the "Safety" side would mean that every time we step down to a lower level of memory
abstraction we would also be obliged to prove termination. So, rather than a _spectrum_, we have a _lattice_ of languages, with non-total languages running parallel to the total ones:

$$
\xymatrix@R=0.1em{
\text{Partial} & & \mathcal{L}_C^\bot & \mathcal{L}_R^\bot & \mathcal{L}_\textbf{1}^\bot \\
\text{Total} & & \mathcal{L}_C & \mathcal{L}_R & \mathcal{L}_\textbf{1} \\
& \text{Liberty} & \ar[rrr] & \ar[ll]  & & \text{Safety} \\
}
$$

The compiler moves from $\mathcal{L}_\textbf{1}$ towards $\mathcal{L}_C^\bot$, and to embed a language from the upper-left corner inside a language towards the lower-right corner requires a proof.

I have yet to completely clarify exactly what these languages would look like. It's my hope that they can share a large amount of syntax, to avoid confusing programmers. Once I work out the details,
I suspect this approach will allow programmers to implement systems in a reasonably high-level way, but breaking some language-based abstractions when necessary, where the only costs to verifiability
come directly from these points were the abstraction is broken. 


#### References


[^1]: After all, nontermination is an effect.
[^2]: An executable specification is implemented in Haskell, but its refinement to the C implementation is proven manually using traditional hoare logic techniques and a C parser.
