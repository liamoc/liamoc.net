---
title: The Trouble with Typing Type as Type
keywords: [ agda, types, theorem-proving, type-theory, foundations, paradox ]
time: 12:00
date: 10th September 2015
---
<div class=hidden>
```
{-#  OPTIONS --type-in-type #-}
module 2015-09-10-girards-paradox where
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Data.Product
```
</div>

Axiomatic set theories such as that of Zermelo and Fraenkel, in their attempt to provide
a comprehensive foundation for mathematics, involve several intricate tricks to avoid becoming
inconsistent. A suitably naïve set theory is already inconsistent due to the infamous paradoxical
set of @Russell.

$$ \Delta = \{ x\ |\ x \notin x \} $$

Here we have used _set comprehension_ to define $\Delta$ as the set of all sets $x$ that do not contain themselves. This leads
to the question, _does $\Delta$ contain $\Delta$_? If $\Delta$ is an element of $\Delta$, then it is not, as $\Delta$ only
contains sets that do not contain themselves. If $\Delta$ is not an element of $\Delta$, then it is, as $\Delta$ does not contain itself --
We have a paradox!

To address this, different foundations take different approaches. Most axiomatic set theories eliminate or restrict the _rule of comprehension_,
that is, they don't allow sets to be constructed from arbitrary predicates. Instead, set comprehension can only be used to describe subsets of already
constructed sets. This prevents comprehension from being used above, but it also prevents a lot of other useful constructions, like products or unions!
Thus a handful of other axioms to construct sets are added, such as pairing, union, powerset and so on (all nicely explained in @Halmos).

Another axiom, that of _regularity_, says[^1] that there is
no infinite sequence $a_n$ such that, for any $k$, $a_k \in a_{k+1}$. This implies that no set can contain itself, and allows us to build the
universe of set theory by _stages_, called _ranks_. At rank zero, no sets exist; at rank one, there is just the empty set; at rank two, there is also the set containing the empty set;
and at each following rank, the added sets all contain the sets that are defined at earlier ranks, as shown in the following figure:

![](./images/vnu.png)

The entire universe of set theory can be thought of as the union of the universe at each rank, $\bigcup_\alpha V_\alpha$, a presentation originally
due to @VonNeumann, but commonly attributed to John von Neumann.

## Moving to Type Theory

This stratification bears remarkable similarity to Russell's theory of _types_ (see @Russell), his own solution to the the paradoxical set $\Delta$,
and the distant ancestor of modern type theory.

Indeed, in the intuitionistic type theory of @MartinLof, the approximate foundation of the Agda proof assistant, we have a heirarchy of types
that very much resembles that of von Neumann or Zermelo[^4]:

$$ \mathsf{Set} : \mathsf{Set}_1 : \mathsf{Set}_2 : \mathsf{Set}_3 : \dots $$

The rule of _cumulativity_, which is not present in Agda[^2], but exists in some type theories and languages such as Idris, makes this resemblance
even stronger:

$$ \dfrac{A : \mathsf{Set}_n}{A : \mathsf{Set}_{n+1}} $$

This rule implies that like the von Neumann rank $V_n$, a type $\mathsf{Set}_n$ is inhabited by every type $\mathsf{Set}_m$ where $m < n$.

The differences between the two theories start to emerge when one examines _why_ this stratification exists in type theory. In axiomatic set theory,
eliminating the axiom of regularity and thus the stratification it implies
makes it rather difficult to do induction, but it does not make the theory inconsistent -- there have been several _non-well-founded set theories_
proposed, such the hyperset theory of @Aczel, which do exactly this. 

Removing unrestricted set comprehension is enough to avoid Russell's paradox, as it allows us to distinguish between _formulae_ (or predicates) and _sets_.
Unlike informal set theory, we cannot construct a set for any given formula. For example,
$\forall x.\ x \notin x$ is a valid formula, but $\{ x\ |\ x \notin x \}$ is _not_ a set.

Type theories are not set theories -- they do not have a separate logical formula language, like that of Frege, to serve as a basis for the
theory. So, one cannot achieve consistency in type theory by restricting how a set may be constructed from a logical formula.
Instead, type theory places restrictions on the kinds of formulae that can be expressed. Rather that rule out paradoxical _sets_ representing
self-referential propositions, type theory rules out _the propositions themselves_. In such a theory, it is not even well-formed to ask if a set contains itself[^5].

This restriction is a consequence of the $\mathsf{Set}$ hierarchy mentioned earlier -- remove this from type theory, by saying instead that
$\mathsf{Set} : \mathsf{Set}$, and the result is more or less equivalent to [Falso](http://inutile.club/estatis/falso/)[^3]. We can show
that type theory is inconsistent with this change using Girard's paradox, which is a generalised encoding of Russell's paradox
for pure type systems. The contradiction derived from this paradox is rather involved, so much so that
Martin-Löf himself didn't realise that it applied to the first version of his type theory. @Hurkens provided a simplification,
which is encoded in Agda [here](http://code.haskell.org/Agda/test/succeed/Hurkens.agda).

With inductive types, however, we can use Russell's paradox directly, by formalising a naïve
notion of sets as comprehensions, and using this to derive a contradiction.

## Russell's Paradox in Agda

For these (interactive) Agda snippets, I have enabled `--type-in-type`, which removes the predicative heirarchy from the type theory, instead stating
that $\mathsf{Set} : \mathsf{Set}$.

```
data SET : Set where
  set : (X : Set) → (X → SET) → SET
```

This defines a set (written `set X f`) as a comprehension over an _carrier type_ `X` and a function `f`, where the element for a given index
value `x : X` is given by `f x`. This definition is already using the fact that $\mathsf{Set} : \mathsf{Set}$ -- normally, a type (of type $\mathsf{Set}$) would not be
permitted as a parameter to `set`, which constructs a type of the same size $\mathsf{Set}$.

The empty set, having no elements, uses the empty type as its carrier :

```
∅ : SET
∅ = set ⊥ ⊥-elim
```

The set containing the empty set, having one element, uses the unit type as its carrier:

```
⟨∅⟩ : SET
⟨∅⟩ = set ⊤ (λ _ → ∅)
```

The next rank, $V_2$, has two elements, and thus can use `Bool` as its carrier:

```
⟨∅,⟨∅⟩⟩ : SET
⟨∅,⟨∅⟩⟩ = set Bool (λ x → if x then ∅ else ⟨∅⟩)
```

More sets could be defined using similar techniques, so I will forgo any further definitions.

We can also define the membership operators for our `SET` type:

```
_∈_ : SET → SET → Set
a ∈ set X f = Σ X (λ x → a ≡ f x)

_∉_ : SET → SET → Set
a ∉ b = (a ∈ b) → ⊥
```

A value of type `a ∈ set X f` can be thought of as a proof that there exists a value `x : X` for which the element function `f` gives `a`.

Using these operators, we can define Russell's paradoxical set $\Delta$ as follows:

```
Δ : SET
Δ = set (Σ SET (λ s → s ∉ s)) proj₁
```

This is a set which, for its carrier type, uses _pairs_ containing a set `s` and a proof that `s` does not contain itself. The element function
just discards the proof, leaving us with the `SET` of all `SET`s that do not contain themselves.

Indeed, we can prove that every set which is in `Δ` does not contain itself:

```
x∈Δ→x∉x : ∀ {X} → X ∈ Δ → X ∉ X
x∈Δ→x∉x ((Y , Y∉Y) , refl) = Y∉Y
```

A corollary of this is that `Δ` itself does not contain itself:
```
Δ∉Δ : Δ ∉ Δ
Δ∉Δ Δ∈Δ = x∈Δ→x∉x Δ∈Δ Δ∈Δ
```

But we know that every set which does not contain itself is in `Δ`:

```
x∉x→x∈Δ : ∀ {X} →  X ∉ X → X ∈ Δ
x∉x→x∈Δ {X} X∉X = (X , X∉X) , refl
```

And from this we can derive a contradiction:

```
falso : ⊥
falso = Δ∉Δ (x∉x→x∈Δ Δ∉Δ)
```

## Musings and Speculation

I find it very curious that two very different approaches to formalising mathematics end up with much the same stratified character, and for
different reasons. Perhaps this Russell-style heirarchy is, kind of like the Church-Turing thesis,
a fundamental characteristic of any sufficiently expressive foundation. Something _discovered_ rather than _invented_. In the words of @DanaScott:

> The truth is that there is only one satisfactory way of avoiding the paradoxes: namely, the use of some form of the _theory of types_.
> That was at the basis of both Russell's and Zermelo's intuitions. Indeed the best way to regard Zermelo's theory is as a simplification
> and extension of Russell's. (We mean Russell's _simple_ theory of types, of course.) The simplification was to make the types _cumulative_.
> Thus mixing of types is easier and annoying repetitions are avoided. Once the later types are allowed to accumulate the earlier ones,
> we can then easily imagine _extending_ the types into the transfinite -- just how far we want to go must necessarily be left open.
> Now Russell made his types _explicit_ in his notation and Zermelo left them _implicit_. [emphasis in original]

## Acknowledgements

The Agda development in this post is taken from one of Thorsten Altenkirch's lectures, the code of which is available [here](http://www.cs.nott.ac.uk/~txa/g53cfr/l20.html/l20.html).
The original proof is, as far as I can tell, due to Chad E Brown, who formulated the same thing in Coq.

#### References

[^1]: This presentation is not the normal one found in textbooks, which is that every non-empty set contains an element
that is disjoint from itself, but that presentation is more brain-bending, and is
implied by the statement presented here if you include the axiom of dependent choice.

[^2]: Agda makes use of explicit _universe polymorphism_ instead, and I'm still undecided which version of type theory I like better.

[^3]: *Falso* is a registered trademark of Estatis, Inc. All Rights Reserved.

[^4]: Here, $\mathsf{Set}$ is the type given to types, similar to the _kind_ `*` in Haskell, and is not a reference to the sets of axiomatic set theory.

[^5]: In set theory, it's a valid question to ask, just the answer is always "no".

