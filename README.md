# system-f-agda


An Agda proof that the erasure of System F with iso-recursive types to System F with equi-recursive types constitutes a fully abstract compiler.
It is based on a pre-existing formalisation of System F in Agda by Sandro Stucki:

  https://github.com/sstucki/system-f-agda

The main results are in src/SystemF/FullAbstraction.agda.
The rest of this file contains the README for the original code by Sandro Stucki.



A formalization of the polymorphic lambda calculus extended with
iso-recursive types

The code in this repository contains an Agda formalization of the
Girard-Reynolds polymorphic lambda calculus (System F) extended with
general recursion and iso-recursive types.  The formalization includes
two variants of an operational call-by-value semantics (small-step and
big-step) with associated type soundness proofs, an equivalence proof
of the two semantics, as well as proofs of decidability of type
checking and uniqueness of typing derivations.

The file `src/README.agda` contains a more detailed overview of the
formalization.


Verifying the formalization
---------------------------

The formalization is written in [Agda](https://github.com/agda/agda)
and makes heavy use of the [Agda standard
library](https://github.com/agda/agda-stdlib).  The code in this
repository has been verified using Agda 2.5.3 and version 0.14 of the
standard library.  The latest versions of the Agda distribution and
standard library, along with setup instructions, can be found at

 * https://github.com/agda/agda
 * https://github.com/agda/agda-stdlib

The easiest way to verify all the code is to compile the `README.agda`
file from the `src/` directory.  Run

    agda src/README.agda -i src -i <path-to-Agda-standard-library>/src

in the console, or simply open the file in the
[Agda Emacs mode](https://github.com/agda/agda#configuring-the-emacs-mode)
and type `C-c C-l`.

Using the Emacs mode one can also run Agda functions interactively in
Emacs by typing `C-x C-n <expression>`.  For example, typing

    C-x C-n typeOf [] (Λ (λ' (var zero) (var zero)))

in the module `SystemF.TypeCheck` runs the type-checking decision
procedure to determine the type of the polymorphic identity function.
It should return

    yes (∀' (var zero →' var zero) , Λ (λ' (var zero) (var zero)))


Source code
-----------

The Agda sources of the formalization are freely available on GitHub:

 * https://github.com/sstucki/system-f-agda


License and copyright
---------------------

See the `LICENSE` file.


------------------------------------------------------------------------
Sandro Stucki -- Copyright (c) 2015 EPFL
