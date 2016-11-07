License
=======

Copyright (c) 2016, Johns Hopkins University Applied Physics Laboratory
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

1. Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its
contributors may be used to endorse or promote products derived from
this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

About
=====

SLMech is a mechanization of
[Separation Logic](https://en.wikipedia.org/wiki/Separation_logic) for
a C-like language embedded in the [Coq](https://coq.inria.fr/)
interactive proof assistant.

SLMech is intended to allow a user to construct program correctness
proofs by specifying a pre-condition and post-condition, and applying
specialized tactics to show that if a program executed in a state
satisfying the precondition terminates, then the final state will
satisfy the postcondition.

SLMech is a work in progress.

To guarantee proof correctness, SLMech is written entirely in Gallina
(the language of Coq). At this time, SLMech still relies on a handful
of additional axioms documented [below](#axioms). We hope to
eliminate as many of these axioms as possible in the near future.

Dependencies
============

SLMech depends on Coq. It has been tested against version 8.5.

Building
========

SLMech includes a simple makefile. To build, you should simple type

```
$ make
```

Alternatively, SLMech can be installed via opam, currently this
requires adding a custom opam for this repository. Adding the pin will
automatically install the SLMech package.

```
$ opam pin add coq-slmech .
```

Related Projects
================

SLMech implements the logical core of the proof environment and can be
used directly in any Coq environment to prove properties of programs
written in the SLMech input language (we prefer GNU Emacs with
ProofGeneral).

However, we believe that customizing the proof experience to
specifically target program verification has the potential to greatly improve the usability of SLMech. To that end, we have prototyped two additional tools:

* [slmc](https://www.github.com/jhuapl-saralab/slmc): a Clang libtooling based compiler for automatically translating (some) C code to SLMech's input language 

* [exterminator](https://www.github.com/jhuapl-saralab/exterminator): a proof of concept, debugger-like user interface for SLMech.

Files
=====

* `SLMech/Memory.v`: Defines the basic model for program heap and
  store as partial functions from disjoint subdomains (`chunk`) to
  values of type `val`

* `SLMech/ProgramData.v`: Definitions for manipulating program data. Defines
  the SLMech program state, grammar and coercion functions for mapping between
  `val` and Coq integers. Includes `Notation` definitions for 
  arithmetic and logical operators used by SLMech code

* `SLMech/ProgramSemantics.v`: Defines big and small step semantic relations
  for the SLMech's statement subgrammar (`term`, `atom`, and `stmt`
  defined in `ProgramData.v`)

* `SLMech/Assertions.v`: Defines basic propositions and operators for
  SLMech state assertions

* `SLMech/SequentialProof.v`: Defines the lemmas and tactics used to
  step through SLMech programs and manipulate state assertions.

* `SLMech/Automation.v`: Additional tactics for manipulating SLMech
  `sprop`s and programs

* `SLMech/HeapString.v`: Library for describing C-style NULL
  terminated strings in the heap

* `SLMech/PLinkedListProperties.v`: Library for describing linked
  lists.

* `Max.v`: Example SLMech program and proof for computing the max of
  two integers

* `Swap.v`: Example SLMech program and proof for swapping two integers.

Program Data Types
==================

SLMech's model for program data types is currently rudimentary. All
program values are represented as Coq values of the inductive type
`val`:

```
Inductive val: Type :=
  | Vundef: val
  | Vsint32 z : sint32_bound z -> val
  | Vuint32 z : uint32_bound z -> val
  | Vsint64 z : sint64_bound z -> val
  | Vuint64 z : uint64_bound z -> val.
```

Where `sint32_bound` etc. are predicates indicating that the value is
within the appropriate bounds.

Notably all `val`s are considered to be the same `size` in the heap
(and the elements of the store are sizeless). This will cause issues
when attempting to prove properties of programs that perform byte
level operations on words.

Additional constructors are necessary for representing addresses as
values, and for additional primitive data types (e.g., `int8_t`).

Due to the use of `Z` as the basic type quantifying the information in
each of the nontrivial constructors, it was helpful to define
`Z_to_uint64`, `Z_to_uint32`, `Z_to_sint64`, and `Z_to_sint32`
functions each having a type of `Z -> option val`.  In the case of
`Z_to_uint64` (resp. `Z_to_uint32`) the output is never `None`, as
overflow behavior is well defined in unsigned types, and so any given
input, `z`, is converted to `z mod 2^{64}` (resp `z mod 2^{32}`) and
the proof given for the constructor that the value is within bounds is
`Z.mod_pos_bound`.  In the other case of `Z_to_sint64`
(resp. `Z_to_sint32`) the input integer is checked, but never changed
and so the proof given to the constructor is inherent in the "vetting"
process.

C-style coercion between integer types within binary expressions is
handled by an explicit function:

```
	promte_arith : (Z -> Z -> Z) -> (option val -> option val -> option val)
```

When either input `option val` is `None` or `Some Vundef` then
`promote_arith` produces a `None` output.  Otherwise, for `f : Z -> Z
-> Z`, `ov1 = Some (valtype1 n _)`, and `ov2 = Some (valtype2 m _)` we
have `promote_arith f ov1 ov2` produces `Z_to_valpromote (f n m)`
where `valpromote` is the expected promotion type of `valtype1` and
`valtype2`.  A similar definition, called `promote_bool`, exists for
lifting `bool` comparators in `Z` to `option bool` comparators in
`option val`.

Composite data types in the heap can be represented by defining
relations between the the base address of the structure and a Coq type
representing the composite data. The `heap_string` predicate defined
in `HeapString.v` is an example of this pattern:

```
Inductive heap_string : option val -> string -> sprop := 
| heap_string_null :
    forall (a : val) (st : state),
      (a ↦ (Z_to_uint64 0)) st ->
      heap_string (Some a) EmptyString st
| heap_string_step :
    forall (a : val) p q  (st : state),
    ((a ↦ Some (vnat (nat_of_ascii p)))☆
	 (heap_string (vadd (Some a) (Z_to_uint64 1)) q)) st -> 
      heap_string (Some a) (String p q) st.
```

A program value is related to a Coq string in a particular state if
either the value points to a value of 0 in the heap and the string is
the empty string, or the value points to a number that is the ASCII
encoding of the first character of the string and the next location in
the heap is related to the tail part of the string.

Program Syntax and Semantics
============================

Syntax
------
Programs, really subroutines, to be analyzed in SLMech follow a
somewhat C-like syntax of statements and expressions embedded in
Coq. The statement types are arranged in a hierarchy of complexity:

```
Inductive term : Type :=
| skip : term
| abort : term
| ret : term.

Inductive atom : Type :=
| terminal : term -> atom
| assign : var -> expr -> atom
| heapload : var -> expr -> atom
| heapwrite : expr -> expr -> atom
| pcons : var -> var -> expr -> atom
| dispose : expr -> atom
| local : var -> term -> atom.

Inductive stmt : Type :=
| atomistic : atom -> stmt
| ifelse : bexpr -> stmt -> stmt -> stmt -> stmt
| while : bexpr -> stmt -> stmt
| atomic : stmt -> stmt
| seq : stmt -> stmt -> stmt.
```

The differentiator is that `term`s do not modify program state,
`atom`s may modify state but do not contain any sub-statements, and
`stmt`s may contain sub-statements. Separating out these three classes
of statements simplifies many proofs that rely on reducing complexity
from `stmt` to `term`.

Notations are defined to provide a more imperative style syntax for
writing SLMech programs. e.g.,

```
((ifelse (x < y)
    (res ≔ y)
    (res ≔ x));;
ret ;;
skip)
```

Semantics
---------

The program semantics of SLMech is given by the `steps` relation
defined in ProgramSemantics.v:

```
	steps : stmt -> (term * state) -> (term * state) -> Prop
```

The first parameter `stmt` should be seen as the current instruction
being considered, the second parameter `(term * state)` as the
`state`, with a `term` modifier of the program before stepping over
the statement given by the first parameter and we think of the third
parameter `(term * state)` as the `state` with `term` modifier that
results from stepping through said `stmt`.

When a `skip` is used as a modifier to the `state`, we consider the
program to have neither returned nor aborted and is continuing along
as per usual.  An `abort` tells us that our program has aborted and
thus no other lines read can change the state or the modifier.
Similarly, a `ret` modifier tells us that the program has stepped
through a `ret` statement, meaning that nothing can change either the
modifier or the state.  We refer to an element of `(term * state)` as
an `extended state`.

Thus the first few cases of `steps` are:

```
  | steps_aborted : (*An aborted state does not change for any given stmt*)
      forall (c : stmt)(s : state),
        steps c (abort, s)(abort, s)

  | steps_returned : (*When hitting a return stmt, you ignore any following statements*)
      forall (c : stmt)(s : state),
        steps c (ret, s)(ret, s)
```

Of the other statement claues, only `while` is particularly
interesting:

```
  (*If some chain of length n reaches a skip, then the loop halts*)
  | steps_while_halt : forall (b : bexpr)(c : stmt) (s1 s2 : state),
                         (exists (n : nat), steps (partial_while b c n) (skip, s1) (skip, s2)) ->
                         steps (while b c) (skip, s1) (skip, s2)

  (*Here we're equivocating between a "real" abort and an infinite loop*)
  | steps_while_abort : forall (b : bexpr)(c : stmt) (s1 s2 : state),
                          (forall (n : nat), steps (partial_while b c n) (skip, s1) (abort, s2)) ->
                          steps (while b c) (skip, s1) (abort, s2)

  (*If some chain of length n reaches a return statement, then the loop halts and goes into a return*)
  | steps_while_ret : forall (b : bexpr)(c : stmt) (s1 s2 : state),
                        (exists (n : nat), steps (partial_while b c n) (skip, s1) (ret, s2)) ->
                        steps (while b c) (skip, s1) (ret, s2)
```

The first clause is the nominal case in which the `while` loop
completes without hitting an abort or a return. The latter two cases
respectively cover an abort or return occuring during execution of the
loop.

The `partial_while` function unrolls the while loop `n` times. This
definition of while limits SLMech to proofs that hold only for a
finite number of loop iterations.

Program Heap Model
==================

As one would expect, the heap is maps addresses (Coq values of type
`addr`) to values (Coq values of type `val`). However, rather than
represent the heap directly as a function or a list of pairs, we
represent it as two separate objects.  The first object is a set,
`domain` with the usual classical set operations and relations
associated with it (union, intersection, subset, etc.).  The second
object is a partial function, `heap\_f` which takes in a `domain` and
an `addr` and outputs a `val`. This division simplifies bookkeeping
when heaps are decomposed, modified, and reconstituted during the
process of reasoning about a programs behavior.

Chunks and Addresses
--------------------

The elements of the `domain` are sets of addresses, known as `chunks`.
These `chunk` objects are added or removed from the domain whenever a
call to `malloc` or `free` occurs.  To ensure that the addresses
contained in each distinct `chunk` is not contained in any other
`chunk` the following axiom was created

```
Axiom chunk_unique :
  forall (c c' : chunk)(a : addr),
    In a c -> In a c' -> c = c'.
```
	
In addition to being the elements of the `chunk` sets, the addresses
are given a total ordering thus meaning that `chunk` sets can be
implemented as `OrderedTypeWithLeibniz`.  This leaves us with some
useful machinery, not the least of which is the canonical listing of
each element in each `chunk`, that comes for free.  Unfortunately, as
the addition of chunks is the newest addition to the heap model, none
of these advantages have been exploited as of yet.  An obvious
suggestion would be to add a `chunk_bits` predicate that would work
in an identical way to the current `store_bits` predicate.

Domains and Partitions
----------------------

As already discussed, the `domain` type is a set of sets of `addr`
types.  Whereas before it was necessary to track how the entire heap
was split into subheaps, it is now only necessary to keep track of how
the domains are split up into disjoint subdomains. The predicate,
`heap_bits`, keeps track of a list of subdomains which partition the
set

```
Inductive heap_bits : list domain -> domain -> Prop :=
| empty_heap : heap_bits nil empty
| non_empty_heap : forall (d k : domain) (l : list domain),
  heap_bits l d
    -> Empty (inter k d)
    -> heap_bits (k::l) (union k d).
```
	
From the above, we can see that this gives us a list of subdomains
that are pairwise disjoint and union to the whole set.  Hence, the
list of subdomains associated with `heap_bits` essentially partition
the set, though we do allow for entries to be empty.  The fixpoint
function `union_list` and the inductive construction `pw_disjoint`
help to characterize `heap\_bits` in a more straightforward manner

```
Fixpoint union_list (l : list domain) : domain :=
  match l with
    | nil => empty
    | a::l' => union a (union_list l')
  end.

Inductive pw_disjoint : list domain -> Prop :=
| pw_disjoint_nil : pw_disjoint nil
| pw_disjoint_cons : forall (a : domain) (l : list domain),
                     Empty (inter a (union_list l)) ->
                     pw_disjoint l ->
                     pw_disjoint (a::l).
```

As we can see `union_list` takes a list of domains and produces their
union.  Next, `pw_disjoint` asserts the domains in a list of domains
are pairwise disjoint.  Thus, as we expect from our intuitive
understanding of the `heap_bits` predicate, we have the following

```
Lemma heap_bits_iff : forall (l : list domain) (d : domain),
                        heap_bits l d <->
                        d [=] union_list l /\
                        pw_disjoint l.
```
						
This is a fairly useful tool in proving various lemmas involving
`heap_bits` such as:

```
Corollary heap_bits_lists_comm :
     forall (d : domain) (l l' : list domain),
          heap_bits (l++l') d -> heap_bits (l'++l) d.
```


The `heap_f` Partial Function
-----------------------------

The second component of a heap is the heap function:

```
heap_f : domain -> addr -> option val
```

This is a partial function that returns `None` if and only if the
address is not in the domain.  The partial functionality is enforced
by two axioms. The first axiom is given by

```
Axiom heap_f_out_of_bounds :
  forall (h : heap_f) (d : domain) (a : addr), 
    ~In' a d <-> h d a = None.
```
	
Which assures that any `heap\_f` function will return `None` on the
sole condition that the address being evaluated is not found in the
domain being evaluated.

The second axiom assures us that as long as an evaluated address is
contained within an evaluated domain the resultant value does not
change when moving to a larger domain

```
Axiom heap_pf :
  forall (h : heap_f) (d d' : domain) (a : addr)(v : val),
    d [<=] d' -> h d a = Some v -> h d' a = Some v.
```

Thus, one is now free to reason about how the domain is partitioned
without needing to reason about reads and writes on the heap.

Program Store Model
===================

The store binds program variables (Coq values of type `var`) to
program values (Coq values of type `val`). It is architected similarly
to the heap as domain of variables, called `locals`, and a partial
function over that domain

```
store_f : locals -> var -> option val
```

As expected a similar set of rules to those in the case of the
`heap_f` type enforces that the `store_f` type behaves as a partial
function.

```
Axiom store_f_out_of_bounds :
	forall (s : store_f) (l : locals) (v : var), 
    ~In v l <-> s l v = None.
	
Axiom store_pf :
  forall (s : store_f) (l l' : locals) (x : var)(v : val),
  l [<=] l' -> s l x = Some v -> s l' x = Some v.
```

The `Var` module (defining the Coq type representing program
variables) has type `OrderedTypeWithLeibniz` which defines an explicit
total ordering onthe variables.  The major advantage to this is that
the `locals` set can be implemented via `MSetList`.  This allows a
`store_bits` predicate which allows us to easily track the
relationship between Coq variables and the program variables they
represent (in particular, that distinct Coq variables always represent
distinct program variables).

```
Definition store_bits l s := elements s = l.
```

Axioms
======

SLMech relies on a handful of axioms beyond the core logic of
Coq. Some of these are necessary to define the behavior of abstract
entities (such as the heap and store functions). Others are
expediencies that we are working to eliminate. The complete list of
axioms is included below.

Memory.v
--------

* `addr_max_pos` asserts that the maximum address value is uint64 max
* `chunk_equality` makes set equality logically equivalent to Leibniz
  equality
* `chunk_unique` asserts that chunks contain unique keys
* `heap_f_out_of_bounds` asserts that a heap function is undefined (`None`) for all
  inputs not in its domain
* `heap_pf` asserts that if a heap function is defined for some input in
  a subdomain, then it has the same value for the same input in a
  larger domain
* `heap_equality` asserts that set equality is equivalent to Leibniz
  equality for domains
* `store_f_out_of_bounds` asserts that a store is undefined (`None`) for all inputs
  not in its domain
* `store_pf` asserts that if a store is defined for some input in a
  locals sublist, then it has the same value for the same input in a
  larger locals list
* `store_equality` asserts that set equality is equivalent to Leibniz
  equality for locals

ProgramData.v
-------------

* `error_vals` asserts that the termination values `ERR_SUCCESS` and
  `ERR_ERROR` are distinct.

ProgramSemantics.v
------------------

* `steps_well_defined` asserts that the small step relation `steps` is a well
  defined function

SequentialProof.v
-----------------

* `bijective_coercion_1` asserts that coercing an address to a value
  and back doesn't change the address

