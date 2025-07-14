---
author: Britt Anderson
title: Can Programming Languages Tell Us How We Think?
tags: 
  - mtmc
---

# Programming Language Features that Cognitive Modelers Don\'t Seem to Talk About

Our cognition is structured. Our spoken languages follow rules, some of
which seem to be universal. Since the same minds that speak, and are
thus constrained, are the ones that designed our programming languages
can we infer anything about how our minds might work from the features
language designers discover and create? Could a recognition of the
relevance lead us to make better choices in the programming language we
choose to implement a cognitive model?

1.  Are our minds lazy? Most of our programming languages use \"eager\"
    evaluation, but some, e.g. Haskell, use \"lazy\" evaluation. For
    example in Haskell I can create a lazy list.

    :::: captioned-content
    ::: caption
    The list is infinite, but Haskell is lazy and only generates what is
    necessary. Since I only asked for the first 11 elements, that is all
    it computes. The rest is a sort of promise. Some refer to this as
    `call-by-need` as opposed to `call-by-value`.
    :::

    ``` {#aLazyList .haskell results="value" exports="both"}
    myil :: [Int]
    myil = [1..]
    take 11 myil
    ```
    ::::

  --- --- --- --- --- --- --- --- --- ---- ----
  1   2   3   4   5   6   7   8   9   10   11
  --- --- --- --- --- --- --- --- --- ---- ----

Maybe we can think of infinity without being able to count to it,
because infinity exists as a promise. We can describe how to get there
and that is good enough.

1.  Do our thoughts have types? Programming languages have \"types.\" A
    value can be an interger or a floating point value. It can be a
    character or a string. We can have lists of integers, and we for
    some languages we can define our own potentially very exotic types.
    This allows the infrastructure of our programming language, the
    interpreters and compilers and such, to operate on our input. We can
    use the types to determine what to do and even overload our
    operators.

    :::: captioned-content
    ::: caption
    The same operator `+`{.verbatim} will add two numbers but
    concatenate two strings. They `types` of the values let it know what
    to do.
    :::

    ``` {#Simple_Python_Types .python results="output" exports="both"}
    string1 = "hello "
    string2 = "world"
    num1 = 1
    num2 = 2
    print (num1 + num2)
    print (string1 + string2)
    ```
    ::::

    ```{=org}
    #+results: Simple_Python_Types
    ```
    ``` example
    3
    hello world
    ```

    Does this notion of a \"type\" exist for our thoughts? At the neural
    level spikes are on or off, but the same is true of all the little
    bits in our computers. Still, the language can superimpose a type on
    these 0/1 patterns. Does our mentalese do the same?

2.  Are our types of thoughts static or dynamic?

    :::: captioned-content
    ::: caption
    Our variable `a` is initially a character. Then it is defined to be
    a number. The type of `a` is altered dynamically.
    :::

    ``` {#Dynamic_Typing .python exports="both" results="output"}
    a = "1"
    a = 1
    b = 2
    print (a + b)
    ```
    ::::

    ```{=org}
    #+results: Dynamic_Typing
    ```
    ``` example
    3
    ```

    :::: captioned-content
    ::: caption
    Trying to force our previously defined integer to be a string
    produces an error in Haskell.
    :::

    ``` {#staticTyping .haskell results="output" exports="both"}
    :set -Wall
    x :: Int
    x = 42
    x = "hello"
    ```
    ::::

    ```{=org}
    #+results: staticTyping
    ```
    ``` example
    <interactive>:4:1: error: [GHC-88464]
        Variable not in scope: x :: Int
    <interactive>:6:1: warning: [GHC-63397] [-Wname-shadowing]
        This binding for ‘x’ shadows the existing binding
          defined at <interactive>:5:1
    ```

    When you learn a fact is it fixed? Can paradoxes of thought be
    brought to the level of static typing?

3.  Are our minds interpreted, compiled or a life long image?
    Interpreted languages read the code line by line and give a
    simultaneous translation. Compiled languages digest an entire
    program at once and output the machine code translation. Images are
    \"live\" and execute and re-define on the fly. Python is typically
    interpreted. Haskell compiled. Common Lisp is an image.

    Anecdotes abound about problems being solved after a good night\'s
    sleep. Is the replay of our dreams the compilation of our
    experiences? Is the real time response to environmental events the
    interpretation of input? Is the constant revision of our lived
    experience best accomodated by the metaphor of the [Lisp
    Image](https://arxiv.org/abs/2110.08993)?

4.  Do our minds engage in metaprogramming?

    :::: captioned-content
    ::: caption
    In some programming languages you can write code that writes code.
    This is best known for Common Lisp, but exists for other languages
    too, e.g. Lean, Julia, and Template Haskell.
    :::

    ``` {#metaprogramming .commonlisp org-language="lisp" results="output"}
    ;; Define a simple conditional macro
    (defmacro unless-zero (number &body body)
      `(unless (= ,number 0)
         ,@body))

    ;; Test the macro
    (unless-zero 5
      (format t "Number is not zero!~%")
      (format t "Its square is: ~a~%" (* 5 5)))

    (unless-zero 0
      (format t "You don't know nothing"))

    (unless-zero 1
      (format t "Number is one!~%"))
    ```
    ::::

    ```{=org}
    #+Caption: Note that one of our evaluations is missing. 
    ```
    ```{=org}
    #+RESULTS: metaprogramming
    ```
    ``` example
    Number is not zero!
    Its square is: 25
    Number is one!
    ```

    We learn many things as we grow and age, and some of those things
    are not simply re-definitions, but deep conceptual changes. How is
    it we learn to learn? How can we reprogram ourselves? Is the concept
    of the metaprogram one we need for any satisfactory account of
    thinking?

# In summary,

Maybe we should think more about what the designers of programming
languages have created when thinking about how to model the thinking
that we do. Maybe thinking about the features of the cognitive process
we are modelling will lead us to favor some programming language over
others as it permits a more natural application of our ideas to the
problem.
