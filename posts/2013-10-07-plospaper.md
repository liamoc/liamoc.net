---
title: Trustworthy File Systems accepted to PLOS
keywords: [ data61, verification, publication, plos, file-systems, cogent ]
date: 7th October 2013
time: 09:00
---

The Trustworthy File Systems project has had a paper accepted into PLOS this year. I am one of
the co-authors.

I think it gives a good overview of our project, our research position, and what we are trying
to achieve. It also gives a few tantalising details about the language I'm working on, CDSL (edit: now called Cogent).

<small>Gabi Keller, Toby Murray, Sidney Amani, Liam O'Connor, Zilin Chen, Leonid Ryzhyk, Gerwin Klein and Gernot Heiser</small> \
**File Systems Deserve Verification Too!** \
*Workshop on Programming Languages and Operating Systems (PLOS), November, 2013*

Full PDF Available from [NICTA's page](http://www.ssrg.nicta.com.au/projects/TS/filesystems.pml).

> File systems are too important, and current ones are too buggy, to remain unverified. Yet the most 
> successful verification methods for functional correctness remain too expensive for current file 
> system implementations — we need verified correctness but at reasonable cost. This paper presents 
> our vision and ongoing work to achieve this goal for a new high-performance flash file system, 
> called BilbyFs. BilbyFs is carefully designed to be highly modular, so it can be verified against 
> a high-level functional specification one component at a time. This modular implementation is 
> captured in a set of domain specific languages from which we produce the design-level 
> specification, as well as its optimised C implementation. Importantly, we also automatically 
> generate the proof linking these two artefacts. The combination of these features dramatically 
> reduces verification effort. Verified file systems are now within reach for the first time.
