---
author: Britt Anderson
date: 25-Aug-2025
title: Exercises for Learning Lean
tags: lean
---

# Finding good learning material for Lean4 is a challenge

Lean4 is version 4 of the [Lean programming language](https://lean-lang.org/lean4/doc/whatIsLean.html). It is intended to
be both an interactive theorem prover and a language for practical
programming. It is well supported and the pace of development is rapid.
Thus, it can be hard to find tutorial material, and the material you
find may be out of date quickly.

I found that claude.ai seemed to have a reasonable grasp of current
introductory Lean and I asked it to write me a series of exercises,
beginning with the trivial, to practice the tactic approach to
interactive theorem proving. I liked the [Natural Number Game](https://adam.math.hhu.de/#/) as a step
0, but then I wanted to move on to using Lean in a more idiomatic way so
that I could also learn the peripheral features necessary to use it
practically. In my case that is Emacs, you are more likely to be using
VS Code. In both cases you need to learn how to use the tool as well as
the language.

I suspect that claude.ai found some exercises somewhere and glued them
together for me. I am happy to give you credit if you recognize them,
but for the convenience of other beginners I link them here.

1.  [Exercises](../assets/lean_exercises_tactics_sorries.lean)
2.  [Solutions](../assets/lean_exercises_tactics_solutions.lean)

I will also be posting a set of exercises on \"Set\" operations and
proofs shortly.

Note Bene: to use these you will probably want to set up a project and
have these files in a module. You can ignore a lot of the project
details as long as you can get your IDE to find the necessary imports
and to give you feedback on the proof as you replace the sorries.
