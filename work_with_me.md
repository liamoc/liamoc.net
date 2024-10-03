---
title: PhD Position (Foundations)
---
Dr. Liam O'Connor, *Foundations Cluster*, School of Computing, Australian National University.

We are looking for PhD students to join me working on topics related to programming languages and formal methods. This is a fully-funded scholarship for a PhD degree at the Australian National University, including a living stipend. Details on the scholarship and formal eligibility criteria are found [here](https://study.anu.edu.au/scholarships/find-scholarship/anu-phd-scholarship). Information about the ANU for postgraduate research can be found [here](https://study.anu.edu.au/apply/postgraduate-research). 

The exact topic can be determined with the candidate, but we are particularly interested in topics in two themes: **Semantic Foundations for Software Engineering**, and **Lightweight Formal Methods for Programming**. Details of each theme are provided below. 

Note that is not a prescription, and candidates wanting to pursue topics in other areas will also be considered. If you are interested in projects with both a strong theoretical component as well as real-world practical impact, please get in touch.

To express interest, please email `me` at this domain or via `liam.oconnor` at `anu.edu.au`. Please include details about yourself such as a CV. Formal applications are via the ANU portal (see [the instructions](https://study.anu.edu.au/apply/postgraduate-research#how-to-apply)) but applicants are encouraged to contact me informally first. 

---

## Semantic Foundations for Software Engineering


### Description 

Software Engineering abounds with tools and languages for specification, modelling, implementation, monitoring, analysis, verification and testing of software systems. These tools, however, are rarely backed up by *formal semantics*. Formalising the semantics of such artefacts has a number of benefits, including:

- Gaining a greater understanding of the meaning of these tools and languages, and how they relate to the software system they concern;
- Providing the groundwork for formal verification of these tools, giving mathematical proofs of the soundness and completeness of these tools, ensuring software safety, liveness and cybersecurity properties;
- Developing insight for the design of new tools and languages amenable to formal treatment.

As software systems become pervasive, the cost of critical bugs and vulnerabilities increases. This has led to a renewed interest in formal guarantees. Developing semantics for such systems is therefore of crucial importance for the development of future software with a high level of assurance.

### Required Skills

A PhD in this area is necessarily quite mathematical, so applicants should be comfortable with discrete mathematics (logic, sets and proofs). Other mathematical topics that may be useful include topology, lattice theory, induction and coinduction, model theory, proof theory, category theory, abstract algebra and mathematical foundations, but familiarity with these is not required.

Essential programming skills and knowledge of algorithms and data structures is also required. In addition, experience in the following areas of computer science is useful, but not required: proof assistants (Lean, Coq, Isabelle/HOL, Agda, etc.), automata theory, computability theory, domain theory, programming languages theory (e.g. operational semantics, types), concurrency theory, functional programming, formal verification.

### Prior Work

In recent years I have been working with my PhD student [Rayhana Amjad](https://rayhana.dev/) to develop semantics for Linear Temporal Logic variants used in runtime verification, monitoring, and testing:

<small>
Rayhana Amjad, Rob van Glabbeek, Liam O'Connor\
**Semantics for Linear-time Temporal Logic with Finite Observations**\
*Expressiveness in Concurrency and Structural Operational Semantics (EXPRESS/SOS)*, Calgary, Canada, 2024.\
Electronic Proceedings in Theoretical Computer Science, to appear.
</small>

Another relevant project, now completed, is Shoggoth, which is the first comprehensive accounting of the semantics of strategic rewriting languages, commonly (but not exclusively) used in particular for the design and modelling of compiler optimisations. This work was part of the PhD project of Dr. Xueying Qin.

<small>
Xueying Qin, Liam O'Connor, Rob van Glabbeek, Peter Höfner, Ohad Kammar and Michel Steuwer\
**Shoggoth: A Formal Foundation for Strategic Rewriting** \
*Principles of Programming Languages (POPL)*, London, UK, 2024. \
Proceedings of the ACM on Programming Languages, Volume 8, January 2024, Article 3, pp 61–89 \
[Available from ACM](https://dl.acm.org/doi/10.1145/3633211)
</small>

---

## Lightweight Formal Methods for Programming

### Description 

In recent years, the success of projects like [seL4](https://sel4.systems/), [CompCert](https://compcert.org/) and Cogent suggest that achieving end-to-end mathematical guarantees of safety and security are not out of reach for foundational software systems, and yet the vast majority of software is developed without such guarantees. The reason is simple: insisting on full, end-to-end formal guarantees of correctness produces projects that are more costly, require greater expertise to develop, and take more time than traditional low-assurance software development. Yet, in the world of formal methods there exist specification languages, automatic analyses, models and systems that can be put to use in low-cost scenarios. These methods improve the reliability of software without dramatically increasing costs.

Examples of such *lightweight formal methods* include property-based testing, first pioneered in the Haskell QuickCheck library, where software systems are tested based on formal (usually algebraic) specifications. Now property-based testing libraries exist for all common programming languages and it enjoys widespread industrial use. 

Another example is *type systems*, arguably the most widely-deployed instance of formal methods in software engineering. Type systems typically ensure type and memory safety properties, but they can be extended with all kinds of analyses to enable developers to couple specifications to their implementations and have them automatically checked by the compiler. At the extreme end of this, with liquid and dependent type systems, full correctness can be verified using type system techniques.

Topics in this theme would revolve around taking techniques established in the formal methods community and applying them to practical software engineering tools and programming languages.

### Required Skills

Applicants in this theme will need strong programming skills, including skill at algorithms and data structures. Experience in Software Engineering is positive. Other computer science areas that are useful for this theme include: automata theory, type systems and programming languages, compilers, software modelling, formal verification, software specification, theorem proving.  Mathematical maturity, particularly in discrete mathematics, is also a plus.

### Prior Work

Three projects of mine come to mind for this theme. The first, [Quickstrom](https://quickstrom.io), is a property-based testing tool which enables acceptance testing of web applications using a testing variant of Linear Temporal Logic called QuickLTL. This project is joint work with Oskar Wickström.
 
<small>
Liam O'Connor, Oskar Wickström\
**Quickstrom: Property-based Acceptance Testing with LTL Specifications** \
*Programming Languages Design and Implementation (PLDI)*, pp. 1025-1038, San Diego, California, USA, June 2022. \
[Available from arXiv](https://arxiv.org/abs/2203.11532)
[Talk Available on YouTube](https://www.youtube.com/watch?v=6t8emhea0pA)
</small>

Another project in this theme is Dargent, an extension to my Cogent language for systems verification, that enables automatic verification of data layouts in memory:

<small>
Zilin Chen, Ambroise Lafont, Liam O'Connor, Gabriele Keller, Craig McLaughlin, Vincent Jackson, Christine Rizkallah\
**Dargent: A Silver Bullet for Verified Data Layout Refinement** \
*Principles of Programming Languages (POPL)*, Boston, Massachusetts, USA, 2023. \
Proceedings of the ACM on Programming Languages, Volume 7, January 2023, Article 47, pp 1369–1395 \
[Available from TS](https://trustworthy.systems/publications/papers/Chen_LOKMJR_23.abstract)
[Talk available on YouTube](https://www.youtube.com/watch?v=IsHzO3F0dSI)
</small>

Another extension to Cogent was integrating it with property-based testing, also relevant to this theme:

<small>
Zilin Chen, Christine Rizkallah, Liam O'Connor, Partha Susarla, Gerwin Klein, Gernot Heiser, Gabriele Keller\
**Property-Based Testing: Climbing the Stairway to Verification** \
*Software Language Engineering (SLE)*, pp. 84-97, Auckland, New Zealand, December 2022. \
Winner of Distinguished Artifact Award.\
[Available from TS](https://trustworthy.systems/publications/papers/Chen_ROSKHK_22.abstract)
</small>
