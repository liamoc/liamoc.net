---
title: Imperative Reasoning is Hard
keywords: [ verification, reasoning, imperative, total, functional, monads, edsls ]
time: 12:00
date: 13th November 2013
---

I believe that the set of languages which are easy to reason about formally and the set of languages in which it is easy to write correct programs intersect heavily. For this
reason, I advocate _total programming_ in _purely functional_ programming languages, as this gives rise to a drastically simpler model for formal reasoning compared to mainstream imperative programming, as well as compared to programming in impure functional languages such as ML which do not separate evaluation from execution of effects.

To illustrate my point, I will verify the correctness of a simple program, first in an 
imperative setting and then in a purely functional setting. Then I will show how we can embed effectful, nonterminating, or nondeterministic computations inside a total, purely functional substrate, and discuss the advantages of this approach.

## Floyd-style Imperative Verification

As an example, I will verify the program $\textbf{SumTo}$, which iteratively adds up all natural numbers to a fixed $K > 1$. The correctness condition is that the result of the computation should be the same as the arithmetic series:

$$ \frac{K(K + 1)}{2} $$

Using an extremely simple imperative language, with only six constructs[^0],

$$ \begin{array}{lclr}
   P & ::= & x := e & \text{(variable assignment)}\\
     & |   & P; P & \text{(sequential composition)}\\
     & |   & P + P & \text{(nondeterministic choice)}\\
     & |   & g & \text{(boolean guard)}\\ 
     & |   & P^* & \text{(repeat zero or more times)}\\ 
     \end{array}
$$

The program $\textbf{SumTo}$ is simply expressed as:

$$i := 1; x := 1; (i < K; i := i + 1; x := x + i)^*; i = K $$

The are a number of ways to ascribe semantics to such a program, but for our purposes we will use a _state transition diagram_ in the style of @Floyd_67. @Hoare developed an equivalent axiomatic semantics that works over language syntax, but I'll use Floyd's method as it is more visual and more immediately intuitive. A _state transition diagram_ consists of a set of _states_ $Q$, _initial_ states $I \subseteq Q$, _final_ states $F \subseteq Q$, a set of variable assignments (_stores_) $\Sigma$, and a set $\Delta$ of _transitions_, where a transition is a quadruple $(Q_i,g,f, Q_f),$ where the guard $g$ is a predicate $\Sigma \rightarrow \mathbb{B}$ and the store update $f$ is a function $\Sigma \rightarrow \Sigma$. 

The diagram for the above $\textbf{SumTo}$ program is:

$$ \xymatrix@C+1em{ *++[o][F-]{S} \ar[r]^{x,i := 1} & *++[o][F-]{L} \ar[d]^{i = K} \ar@/^/^{i < K;\ i := i + 1}[r]  &*++[o][F-]{A}  \ar@/^/^{x := x + i}[l]  \\
   & *++[o][F=]{T}  &   } $$

The state sets are $Q = \{S,L,A,T\}, I = \{S \}, F = \{ T \}$, and the set of transitions $\Delta$ is:

$$ \begin{array}{lllll} 
  \{  & (S, & \lambda \sigma.\ \text{True}, & \lambda \sigma.\ \sigma [x := 1] [i := 1], & L) \\
  ,   & (L, & \lambda \sigma.\ \sigma [i] < K, & \lambda \sigma.\ \sigma [i := \sigma[i] + 1], & A) \\
  ,   & (A, & \lambda \sigma.\ \text{True}, & \lambda \sigma.\ \sigma [x := \sigma[x] + \sigma[i]], & L) \\
  ,   & (L, & \lambda \sigma.\ \sigma [i] = K, & \lambda \sigma.\ \sigma, & T) \\
  \}  \end{array} $$

As the projection notation is somewhat difficult to read, I shall use the semantic brackets $\llbracket \rrbracket$ to denote the store-dependent function corresponding to an expression involving store projections. For example, $\llbracket i := i + 1 \rrbracket$ is equivalent to $\lambda \sigma.\ \sigma [i := \sigma[i] + 1]$. Thus $\Delta$ becomes:

$$ \begin{array}{lllll} 
  \{  & (S, & \llbracket \text{True} \rrbracket, & \llbracket x, i := 1 \rrbracket, & L) \\
  ,   & (L, & \llbracket i < K \rrbracket, & \llbracket i := i + 1 \rrbracket, & A) \\
  ,   & (A, & \llbracket \text{True} \rrbracket, & \llbracket x := x + i \rrbracket, & L) \\
  ,   & (L, & \llbracket i = K \rrbracket, & \lambda \sigma.\ \sigma, & T) \\
  \}  \end{array} $$

 The correctness statement for an imperative program takes the form of a _precondition_ and a _postcondition_, both predicates on the store. In this example, the correctness statement is:

 $$  \Bigg\{ \text{True} \Bigg\}\ \textbf{SumTo}\ \Bigg\{ x = \frac{K(K+1)}{n} \Bigg\}$$ 

That is, under all circumstances, $\textbf{SumTo}$ will leave $x = \frac{K(K+1)}{n}$ once it has terminated.

 To prove correctness,  each state is given  an associated _assertion_ $\Sigma \rightarrow \mathbb{B}$. The assertions on the initial states are implied
 by the precondition, in this case $\llbracket \text{True} \rrbracket$, and the assertions on the final states in turn imply the postcondition, in this case $\left\llbracket  x = \frac{K(K+1)}{n}  \right\rrbracket:$


$$ \xymatrix{ *++[F-:<5em>]{\scriptstyle\text{True}} \ar[r]^{x,i := 1} &*++[o][F-]{ L } \ar[d]^{i = K} \ar@/^/^{i < K;\ i := i + 1}[r]  &*++[o][F-]{A}  \ar@/^/^{x := x + i}[l]  \\
                & *++[F=:<5em>]{\scriptstyle x = \frac{K(K + 1)}{2}}  &   } $$                           

We now must devise some assertions for $L$ and $A$, such that the _assertion network is inductive_, that is, each transition takes us from one assertion to the next:

$$ \begin{array}{lclcl}
      \llbracket{\text{True}} \rrbracket\ \sigma & \land & \llbracket{\text{True}} \rrbracket\ \sigma & \implies & (\text{Assertion}_{L} \circ \llbracket x,i := 1 \rrbracket)\ \sigma \\
      \text{Assertion}_{L}\ \sigma & \land & \llbracket{i < K} \rrbracket\ \sigma & \implies & (\text{Assertion}_{A} \circ \llbracket i := i + 1 \rrbracket)\ \sigma \\      
      \text{Assertion}_{A}\ \sigma & \land & \llbracket\text{True} \rrbracket\ \sigma & \implies & (\text{Assertion}_{L} \circ \llbracket x := x + i \rrbracket)\ \sigma \\      
      \text{Assertion}_{L}\ \sigma & \land & \llbracket{i = K} \rrbracket\ \sigma & \implies & (\llbracket x = \frac{K(K+1)}{2}\rrbracket \circ \lambda \sigma.\ \sigma)\ \sigma
   \end{array} $$

Determining the assertion for $L$ (the _loop invariant_) requires some creativity. Note from the final requirement in the list that 

$$\text{Assertion}_L\ \sigma \land  \llbracket{i = K} \rrbracket\ \sigma  \implies  \left\llbracket x := \frac{K(K+1)}{2}\right\rrbracket\ \sigma$$

So, one might be tempted to simply set $\text{Assertion}_L = \llbracket x = \frac{K(K+1)}{2}\rrbracket$, thus trivially implying the desired conclusion, however this breaks the first requirement

$$ \left\llbracket x = \frac{K(K+1)}{2}\right\rrbracket (\llbracket x,i := 1 \rrbracket\ \sigma)$$

as $1 \neq \frac{K(K+1)}{2}$ for any $K > 1$. So, the assertion must be the only other sensible option:  set $\text{Assertion}_L = \llbracket x = \frac{i(i+1)}{2}\rrbracket$.
This satisfies all the requirements, and easily prescribes an assertion for $A$ as well:

$$ \xymatrix@C+2em{ *++[F-:<5em>]{\scriptstyle\text{True}} \ar[r]^{\!\!\!\!x,i := 1} &*++[F-:<5em>]{ \scriptstyle x = \frac{i(i + 1)}{2} } \ar[d]^{i = K} \ar@/^/^{i < K;\ i := i + 1}[r]  &*++[F-:<5em>]{\scriptstyle x = \frac{i(i - 1)}{2}}  \ar@/^/^{x := x + i}[l]  \\
                & *++[F=:<5em>]{\scriptstyle x = \frac{K(K + 1)}{2}}  &   } $$       

As this assertion network is inductive, I have shown _partial correctness_, that is, _if the program terminates_, it will have a correct result, *but I have  still not proven termination!*  To prove termination, I must additionally choose a well-ordered set[^1] $O$ and associate with each state a function $\text{Rank}_Q : \Sigma \rightarrow O$, which need only be defined when $\text{Assertion}_Q$ is true. For this example, I choose for $O$ the set of pairs $(\mathbb{N} \times \mathbb{B})$, where the ordering is lexicographic comparison[^2], and ranking functions as indicated in the following diagram:

$$ \xymatrix@C+2em{ *++[F-:<5em>]{\scriptstyle(K + 1,\text{False})} \ar[r]^{x,i := 1} &*++[F-:<5em>]{\scriptstyle(K - i + 1,\ \text{False})} \ar[d]^{i = K} \ar@/^/^{i < K;\ i := i + 1}[r]  &*++[F-:<5em>]{\scriptstyle(K - i + 1,\ \text{True})}  \ar@/^/^{x := x + i}[l]  \\
                & *++[F=:<5em>]{\scriptstyle(0, \text{False})}  &   } $$

Then show, for each transition $(Q_s, g, f, Q_f) \in \Delta$, that:

$$\text{Assertion}_{Q_s}\ \sigma \land g\ \sigma \implies \text{Rank}_{Q_s}\ \sigma > \text{Rank}_{Q_f}\ (f\ \sigma)$$

In other words, that each transition decreases the rank, according to the wellfounded order. Wellfoundedness implies there is a point, after some finite number of transitions has been taken, where the rank reaches the minimum element in the ordering -- it can no longer be decreased. Thus, it is impossible to continue taking transitions beyond that point, as all transitions must decrease the rank. Therefore, the program always terminates after a finite amount of transitions.

These obligations are trivial to discharge in our example, which means the algorithm is at last proven correct. This verification was _a lot of work_ to prove something _extremely simple_! I had to define a state transition system, assertion network, loop invariants, a termination order, ranking functions, and prove a bunch of irritating obligations.

## The Purely Functional Approach

For the purely functional version of this algorithm, I will assume the simply typed lambda calculus of @Church equipped with an inductive type for natural numbers $\mathbb{N}$, with constructors $0$ and $\mathtt{suc}$, and a catamorphism $\mathtt{cata}$. The typing rules are as follows:

$$\dfrac{(x : \tau) \in \Gamma}{\Gamma \vdash x : \tau} \quad \dfrac{\Gamma \vdash x : (\rho \rightarrow \tau) \quad \Gamma \vdash y : \rho}{\Gamma \vdash x\ y : \tau}
 \quad \dfrac{\Gamma, x : \tau \vdash e : \rho}{\Gamma \vdash \lambda(x :: \tau).\ e : \tau \rightarrow \rho} $$

$$ \dfrac{ }{ \Gamma \vdash 0 : \mathbb{N}} \quad \dfrac{ \Gamma \vdash n : \mathbb{N} }{ \Gamma \vdash \mathtt{suc}\ n : \mathbb{N}} \quad \dfrac{\Gamma \vdash z : \tau \quad \Gamma \vdash s : \tau \rightarrow \tau}{\Gamma \vdash \mathtt{cata}\ z\ s : \mathbb{N} \rightarrow \tau }$$

$$ \dfrac{ \Gamma \vdash a : \tau \quad \Gamma \vdash b : \rho}{ \Gamma \vdash (a,b) : \tau \times \rho} \quad \dfrac{\Gamma \vdash p : (\tau \times \rho)}{\Gamma \vdash p_1 : \tau} \quad \dfrac{\Gamma \vdash p : (\tau \times \rho)}{\Gamma \vdash p_2 : \rho} $$

The program $\textbf{SumTo}$ is defined as[^3]:

$$ \textbf{SumTo} = \lambda(K :: \mathbb{N}).\ (\mathtt{cata}\ (1,0)\ (\lambda (p :: \mathbb{N} \times \mathbb{N}).\ (p_1 + 1, p_2 + p_1))\ K)_2 $$

The semantics of this language are given via a term rewriting system, where $e[a/x]$ is a capture avoiding substitution of $a$ for $x$ inside $e$.

$$ \begin{array}{lcl} (\lambda(x :: \tau).\ e)\ a & \mapsto & e[a/x] \\
                      (a,b)_1 & \mapsto & a \\
                      (a,b)_2 & \mapsto & b \\
                      \mathtt{cata}\ z\ s\ 0 & \mapsto & z \\
                      \mathtt{cata}\ z\ s\ (\mathtt{suc}\ n) & \mapsto & s\ (\mathtt{cata}\ z\ s\ n)
    \end{array} $$

As this term rewriting system is _confluent_, these rules can be applied to any subexpression in any order and still end up at the same result, and as well-typed terms are _strongly normalising_, the rules only need be applied a finite number of times before the program halts. The proof of this is nontrivial, but it is a property of the ambient calculus, rather than a property of the program being verified. This means I do not need to prove termination, as it would be impossible to express a non-terminating program in this language[^4][^5]. 

Now the correctness statement is, for all $K > 0$:

  $$ (\mathtt{cata}\ (1,0)\ (\lambda (p :: \mathbb{N} \times \mathbb{N}).\ (p_1 + 1, p_2 + p_1))\ K)_2 \stackrel{\star}{\mapsto} \frac{K(K + 1)}{2} $$

Proving the stronger statement

  $$ \mathtt{cata}\ (1,0)\ (\lambda (p :: \mathbb{N} \times \mathbb{N}).\ (p_1 + 1, p_2 + p_1))\ K \stackrel{\star}{\mapsto} \left(K + 1,\frac{K(K + 1)}{2}\right) $$

instead gives better induction characteristics, and it still implies the original correctness statement.

By induction, when $K = 0$, we have:

$$ \begin{array}{ll} & (\mathtt{cata}\ (1,0)\ (\lambda (p :: \mathbb{N} \times \mathbb{N}).\ (p_1 + 1, p_2 + p_1))\ 0) \\
\mapsto & (1,0) \\
= &  (0 + 1, \frac{0(0 + 1)}{2})\ \text{as required} \end{array}$$

When $K = \mathtt{suc}\ n$, we have the induction hypothesis that:

  $$ (\mathtt{cata}\ (1,0)\ (\lambda (p :: \mathbb{N} \times \mathbb{N}).\ (p_1 + 1, p_2 + p_1))\ n) \stackrel{\star}{\mapsto} \left(n + 1, \frac{n(n + 1)}{2}\right) $$

Using this, we can show our goal for $\mathtt{suc}\ n$:

$$ \renewcommand*{\arraystretch}{2}\begin{array}{ll} & (\mathtt{cata}\ (1,0)\ (\lambda (p :: \mathbb{N} \times \mathbb{N}).\ (p_1 + 1, p_2 + p_1))\ (\mathtt{suc}\ n)) \\
  \mapsto & (\lambda (p :: \mathbb{N} \times \mathbb{N}).\ (p_1 + 1, p_2 + p_1))\ (\mathtt{cata}\ (1,0)\ (\lambda (p :: \mathbb{N} \times \mathbb{N}).\ (p_1 + 1, p_2 + p_1))\ n) \\
\stackrel{\star}{\mapsto} & (\lambda (p :: \mathbb{N} \times \mathbb{N}).\ (p_1 + 1, p_2 + p_1))\  (n + 1, \frac{n(n + 1)}{2}) \\
\mapsto & (n + 1 + 1, \frac{n(n + 1)}{2} + (n + 1))\\
= & \left(n + 1 + 1, \dfrac{n(n + 1) + 2(n + 1)}{2}\right)\\
= & \left(\mathtt{suc}\ n + 1, \dfrac{(\mathtt{suc}\ n)(\mathtt{suc}\ n + 1)}{2}\right)\ \text{as required} \end{array}$$

Thus, the program is correct, by induction on the input $K$. The beauty of this approach is that there is nothing in this proof method that would be unfamiliar to anyone who studied a little discrete mathematics and high-school algebra. The lambda calculus is just like an algebraic expression language, and we can reason about it much like we would reason about conventional algebraic expressions: induction, substitution, equational reasoning, and so on.

In addition, because we are reasoning in a _confluent_ rewriting system, the order in which subexpressions are reduced _does not matter_. This is not just convenient for reasoning, it also means that a compiler for this language is free to evaluate expressions in whatever order it likes - be it strict evaluation, parallel evaluation, call-by-need, or anything else. Optimisations such as loop fusion and deforestation are possible, because the compiler is free to rewrite inefficient expressions to an efficient expression, so long as it is reduction-equivalent. Code can be trivially parallelised by adding annotations.

## Bringing Back Effects

These all seem like desirable properties, but there's a sense that in order to achieve those benefits, we've divorced ourselves from the real world. We've limited ourselves to a total, deterministic, effect-free language, but a language like that is merely a space-heater - it can't even display the results it has computed! 

A common way to add some of this missing power to a lambda calculus is to add some side-effects to evaluation. This is the approach taken by impure functional languages such as ML. These languages simply add to the lambda calculus some primitives that represent assignment, and types that represent references (mutable variables)[^6]:

$$ \dfrac{\Gamma \vdash r : \tau\ \textbf{ref}}{\Gamma \vdash\ !r : \tau}  \quad \dfrac{  \Gamma \vdash r : \tau\ \textbf{ref} \quad \Gamma \vdash e : \tau}{ \Gamma \vdash r := e : \tau } $$

To specify semantics for these operations, however, we must bring back our old friend $\Sigma$, the store of variable assignments. 

$$ \dfrac{e\ \text{is fully evaluated}}{(\Sigma, r := e) \mapsto (\Sigma[r := e], e)}  \quad \dfrac{(\Sigma, e) \mapsto (\Sigma', e')}{(\Sigma, r := e) \mapsto (\Sigma', r := e')}  $$

This in turn forces us to be more prescriptive about the order in which expressions are evaluated, making the rewrite system into an _operational semantics_:

$$ \dfrac{a\ \text{is fully evaluated}}{(\Sigma, (\lambda x.\ e)\ a) \mapsto (\Sigma, e[a/x])}  \quad \dfrac{(\Sigma, a) \mapsto (\Sigma', a')}{(\Sigma, (\lambda x.\ e)\ a) \mapsto (\Sigma', (\lambda x.\ e)\ a')} \quad \dfrac{(\Sigma, f) \mapsto (\Sigma',f')}{(\Sigma,f\ a) \mapsto (\Sigma',f'\ a)}$$
$$ \text{ and so on } $$

Without this explicit ordering, we could derive two different results from the same computation, simply by evaluating assignments in a different order. Now that we've added an ordering, however, _we lose the advantages of the pure model_. We have prescribed a specific evaluation model (in this case strict evaluation) on our expressions, so we can no longer reduce arbitrary subexpressions while reasoning, optimisations such as fusion are much more difficult to perform soundly, the user has no control over evaluation (for example for parallelism or laziness), and to properly reason about our programs we are forced to use cumbersome state-assertion reasoning frameworks, just like in imperative languages.

An ideal language supports _both_ purely functional programs where that's appropriate, _and_ impure imperative programs where that's appropriate, with sound reasoning about either style as necessary. With ML's approach, the imperative reasoning _infects_ the purely functional world, and complicates the programmer's mental model. 

A better approach is to _embed_ an imperative language inside the lambda calculus as a separate type. As this embedding requires polymorphism, we'll switch from the simply typed lambda calculus to a variation on the Girard-Reynolds polymorphic lambda calculus [@Reynolds], with data types and syntax loosely inspired by that of [Isabelle/HOL](http://isabelle.in.tum.de/) [@Nipkow].

$$ \begin{array}{lclr}
   \textbf{datatype}\ \alpha\ \mathtt{io} & = & \mathtt{Assign}\ (\alpha\ \textbf{ref})\ \alpha & \text{(variable assignment)}\\
     & |   & \mathtt{Read}\ (\alpha\ \textbf{ref}) & \text{(read variable)}\\      
     & |   & \mathtt{Choose}\ (\alpha\ \mathtt{io})\ (\alpha\ \mathtt{io}) & \text{(nondeterministic choice)}\\
     & |   & \mathtt{Guard}\ \mathbb{B}\ \alpha & \text{(boolean guard)}\\      
     & |   & \mathtt{Loop}\ \alpha\ (\alpha \rightarrow \alpha\ \mathtt{io}) & \text{(repeat zero or more times)}\\ 
     & |   & \mathtt{Bind}\ (\beta\ \mathtt{io})\ (\beta \rightarrow \alpha\ \mathtt{io}) & \text{(sequential composition)}\\     
     & |   & \mathtt{Return}\ \alpha & \text{(return pure value)}\\ 
   \end{array}$$

The type $\alpha\ \mathtt{io}$, denotes an _embedded imperative computation_[^7] which, when _executed_, results in a value of type $\alpha$. We use the infix operator $\gg\!\!=$ for $\mathtt{Bind}$, and $a \gg b$ as a shorthand for $a \gg\!\!= \lambda x.\ b$. 

Then, an imperative $\textbf{SumTo}$ can be expressed directly in this embedded language, notably doing away with the reference $x$:

$$ \begin{array}{rl}  & \mathtt{Assign}\ i\ 1 \\  
 \gg & \mathtt{Loop}\ 1\ \begin{array}[t]{ll}(  \lambda x. & \mathtt{Read}\ i \\
                                         \gg\!\!= \lambda i_v. & \mathtt{Guard}\ (i_v < K)\ \top \\
                                         \gg & \mathtt{Assign}\ i\ (i_v + 1) \\
                                         \gg\!\!= \lambda i_v. & \mathtt{Return}\ (x + i_v) 
                                         )\end{array}\\
 \gg\!\!= \lambda x. & \mathtt{Read}\ i \\
 \gg\!\!= \lambda i_v. & \mathtt{Guard}\ (i_v = K)\ x \end{array}$$

Note that the reduction rules for
the underlying lambda calculus are _unchanged_ - The embedded $\mathtt{io}$ computation is _not_ executed when it is evaluated! Instead, we have a _pure_ computation, which returns an _impure_ computation in an embedded language. This impure computation is then interpreted by an entirely _separate_ set of semantics, defined operationally as the relation
$\leadsto$.

$\mathtt{Guard}$ statements only progress when the condition is true, returning the given value.  

$$ \dfrac{}{ (\Sigma, \mathtt{Guard}\ \text{True}\ v) \leadsto (\Sigma, \mathtt{Return}\ v)}$$

$\mathtt{Bind}$ statements execute the first action until it returns a result, and then use that result to determine the next action:

$$ \dfrac{(\Sigma, a) \leadsto (\Sigma', a')}{ (\Sigma, \mathtt{Bind}\ a\ b) \leadsto (\Sigma', \mathtt{Bind}\ a'\ b)} 
\quad \dfrac{(\Sigma, a) \leadsto (\Sigma', \mathtt{Return}\ v)}{ (\Sigma, \mathtt{Bind}\ a\ b) \leadsto (\Sigma', a\ v)}  $$

Nondeterministic choice is modelled by having two rules, both of which are equally applicable to a given state:

$$ \dfrac{}{ (\Sigma, \mathtt{Choose}\ a\ b) \leadsto (\Sigma, a)} \quad  \dfrac{}{ (\Sigma, \mathtt{Choose}\ a\ b) \leadsto (\Sigma, b)} $$

Loops are given semantics by simple expansion to nondeterministic choice:

$$ \dfrac{}{ (\Sigma,\mathtt{Loop}\ a\ b) \leadsto (\Sigma, \mathtt{Choose}\ (\mathtt{Return}\ a)\ (\mathtt{Bind}\ (b\ a)\ (\lambda a'.\ \mathtt{Loop}\ a'\ b))) } $$

And $\mathtt{Assign}$ and $\mathtt{Read}$ behave exactly as one might expect:

$$ \dfrac{}{(\Sigma, \mathtt{Assign}\ r\ e) \leadsto (\Sigma[r := e], e)} \quad \dfrac{}{(\Sigma, \mathtt{Read}\ r) \leadsto (\Sigma, \mathtt{Return}\ \Sigma[r])} $$

Note that these semantics say nothing about _evaluation of expressions_, only the _execution of actions_. The top-level interpretation for this programming language simply _interleaves_ the execution of actions and the evaluation of expressions. This is because expression evaluation is purely functional - the embedded $\mathtt{io}$ language doesn't care about the order of expression evaluation, because it doesn't change the result of the program! This means we have kept all the benefits of total, deterministic, purely functional programming, while still being able to express partial, nondeterministic, imperative programs using the embedded language when necessary. We have the best of both worlds! 

The drawback is that for imperative programs that _are_ total, terminating, deterministic and otherwise easy to reason about, such as $\textbf{SumTo}$, the reasoning tools available are for the more general $\mathtt{io}$ language - we'd have to prove termination, totality, determinism and so on _for each program we write_. We have all the reasoning benefits of purely functional programming for purely functional programs, but the moment a single mutable variable sneaks its way into a program, it has to go back to the $\mathtt{io}$ sin-bin. The solution is in _another_ embedded language, but a slightly less unwieldy one -- terminating and deterministic:

$$ \begin{array}{lclr}
   \textbf{datatype}\ \alpha\ \mathtt{dtio} & = & \mathtt{Assign'}\ (\alpha\ \textbf{ref})\ \alpha & \text{(variable assignment)}\\
     & |   & \mathtt{Read'}\ (\alpha\ \textbf{ref}) & \text{(read variable)}\\      
     & |   & \mathtt{BoundedLoop}\  \mathbb{N}\ \alpha\ (\alpha \rightarrow \alpha\ \mathtt{dtio}) & \text{(repeat n times)}\\ 
     & |   & \mathtt{Bind'}\ (\beta\ \mathtt{dtio})\ (\beta \rightarrow \alpha\ \mathtt{dtio}) & \text{(sequential composition)}\\     
     & |   & \mathtt{Return'}\ \alpha & \text{(return pure value)}\\ 
   \end{array}$$

The semantics for $\mathtt{dtio}$ are given simply as a mapping into $\mathtt{io}$:

$$ \begin{array}{l}
  \textbf{function}\ \text{interpret}\ ::\ \ \alpha\ \mathtt{dtio}\ \rightarrow\ \alpha\ \mathtt{io} \ \textbf{where}\\
  \begin{array}{lcl}
  \text{interpret}\ (\mathtt{Assign'}\ r\ x) & = & \mathtt{Assign}\ r\ x \\
  \text{interpret}\ (\mathtt{Read}\ r) & = & \mathtt{Read}\ r \\
  \text{interpret}\ (\mathtt{Bind'}\ a\ b) & = & \mathtt{Bind}\ (\text{interpret}\ a)\ (\text{interpret} \circ b) \\
  \text{interpret}\ (\mathtt{Return'}\ x) & =&  \mathtt{Return}\ x \\
  \text{interpret}\ (\mathtt{BoundedLoop}\ n\ a\ b) &=& \mathtt{Loop}\ (0,a) \begin{array}[t]{ll}
               (\lambda r. & \mathtt{Guard}\ (r_1 < n)\ \top \\
               \gg & \text{interpret}\ (b\ r_2) \\
               \gg\!\!= \lambda r'. & \mathtt{Return}\ (r_1 + 1, r') ) \\               
               \end{array} \\
               & & \gg\!\!= \lambda r.\ \mathtt{Guard}\ (r_1 = n)\ r_2 \\
  \end{array}
\end{array} $$

Of course, it is necessary to prove that the output of $\text{interpret}$ is indeed a deterministic $\mathtt{io}$ computation that always terminates, but once this is proven, there is no longer any need to prove these properties for each of our programs. Simply by _expressing_ $\textbf{SumTo}$ in $\mathtt{dtio}$, we have shown it to terminate:

$$ \begin{array}{rl}  & \mathtt{Assign'}\ i\ 1 \\  
 \gg & \mathtt{BoundedLoop}\ K\ 1\ \begin{array}[t]{ll}(  \lambda x. & \mathtt{Read'}\ i \\
                                         \gg\!\!= \lambda i_v. & \mathtt{Assign'}\ i\ (i_v + 1) \\
                                         \gg\!\!= \lambda i_v. & \mathtt{Return'}\ (x + i_v) 
                                         )\end{array}\\
 \end{array}$$
     
One could also imagine using similarly restricted languages to ensure, by construction, that more domain-specific properties are satisfied -- The use of restricted languages to generalise verification of such properties from _one program_ to _many programs_ is precisely the method of the Trustworthy File Systems project I work on at NICTA [@nicta_7248]. 
 
This doesn't just give us the best of both worlds, it lets us pick one of an infinite variety of worlds to live in -- the world of terminating imperative programs, the world of purely functional programs, the world of nondeterministic programs, or even the world of [STM transactions](http://www.haskell.org/haskellwiki/Software_transactional_memory), where access to IO must be restricted for the transactional abstraction to be safe [@Harris]. We can pick whatever sublanguage we want, with whatever reasoning characteristics we want, and thus easily establish properties about our programs almost for free -- they come from the language used, not the program definition. In addition, as @Wadler notes, these languages all have the same monadic structure, which allows high-level operations to be expressed in terms of the monad abstraction rather than in terms of any particular language.  

 All of this is only possible because we have a pure, total substrate within which these languages are embedded. I could define a $\mathtt{dtio}$ language or an $\mathtt{STM}$ language but it would be useless if the ambient lambda calculus was not so restricted -- there is no way to prevent IO during an STM transaction or a diverging expression from being invoked from inside a $\mathtt{dtio}$, when evaluation could have such an effect. 

Lastly, it's worth noting that the Haskell programming language differs from the lambda calculus used here in several important respects. Chiefly, it allows partiality and general recursion, making the language turing-complete.  This still falls under the definition of "purely functional" -- indeed, its non-strict semantics make the sort of reasoning I used here relatively harmless, even in the presence of "bottom" values arising from nontermination or partiality [see @FastAndLoose].  @Turner has advocated strongly for language-enforced totality, but my impression is that total programming is still a fledgling idea, with some distance to cross before it is practical.



#### References



[^0]: The variables $e$ and $g$ stand for arithmetic and boolean expressions, respectively.  
[^1]: That is, a set equipped with a greater-than relation such that each descending chain $v_1 > v_2 > v_3 > \cdots > v_n$ is finite.
[^2]: True is considered greater than False.
[^3]: With standard implementation of addition: $a + b = \mathtt{cata}\ a\ (\lambda(n :: \mathbb{N}).\ \mathtt{suc}\ n)\ b$
[^4]: Even if we added a fixpoint loop combinator as a primitive, making the language turing-complete, we could easily prove termination of $\textbf{SumTo}$ by noting that it never uses it.
[^5]: The imperative language could have used a _bounded_ loop primitive instead of the unbounded one, and also been automatically terminating, but this is not reflective of idiomatic imperative programming, where the same looping construct is used for both infinite and terminating loops. We will examine terminating imperative languages later in the article.
[^6]: Destructive update is perhaps the thorniest effect to deal with, so handling for other effects like console output are left as an exercise.
[^7]: It just so happens that this embedded language forms a monad, but monads are not the salient point here.
