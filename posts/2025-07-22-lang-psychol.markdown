---
author: Britt Anderson
title: A language for theoretical psychology
---

```{=org}
#+tags: mtmc
```
Psychology, across all its sub-disciplines, has generated impressive amounts of data over the last century. However it has at the same time dropped its reason for being. 

Psychology was founded as the science of subjectivity aiming to apply scientific principles and procedures to the
study of consciousness and mental states. The difficulty of this undertaking led to its abandonment and replacement by behaviorism where the black-box was sealed and the science became about discovering connections between sensory inputs and behavioral outputs. 

A brief return towards psychology\'s original purpose was made by the
cognitive psychologists in the 1950s and 1960s building upon
Shannon\'s information theory. After another 20 years this project was
largely replaced again by a new behaviorism where neural correlates were
interposed between stimuli and behavior. The black-box remained sealed. New names, such as
cognitive neuroscience, camouflaged the old approach

While many potential explanations for this evolution exist, I propose
that it largely rests on the absence of a common grounding language
for the expression of theoretical ideas in psychology. We need a language
which permits comparisons across subfields and that makes it easy to express theories well and difficult to express proto-theories and pseudo-theories.

Mathematics offers
many potential candidates. But particularly important is that this language make clear how to test predictions of the theories and how to disconfirm alternatives. As people have a limited capacity for logic and following a highly branched decision tree for multiple steps, computer simulations will be essential. Thus, another desiderata for our
mathematical language is that it provide a direct, transparent, auditable
trail between math and code. 

Ideally the code would not be merely a means of translating math to machine code,  but would itself offer abstractions that fostered new insights into the explanatory
value of the theory. 

The mathematical language proposed
is category theory. In particular the language of monoidal categories. A monoidal category has
notions of both serial and parallel processing. The monoidal category
of corresponding to a hypergraph seems particularly suited to framing psychological theories in a consistent way.

The requisite computer language should aid human understanding; not just instruct the machine. The programming
language should not be merely an implementation detail, but in its own right aid understanding and insight. The functional languages deserve most consideration. The benefit of dependent types, meta-programming and lazy evaluation make Lean the best available option. 
