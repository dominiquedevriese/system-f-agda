------------------------------------------------------------------------
-- A formalization of the polymorphic lambda calculus extended with
-- iso-recursive types
------------------------------------------------------------------------

-- Author: Sandro Stucki
-- Copyright (c) 2015 EPFL

-- The code in this directory contains an Agda proof that the erasure of System
-- F with iso-recursive types to System F with equi-recursive types constitutes
-- a fully abstract compiler.
--
-- It is based on a pre-existing formalisation of System F in Agda by Sandro Stucki:
--
--   https://github.com/sstucki/system-f-agda
--
-- The main results are in SystemF/FullAbstraction.agda.
-- The rest of this file contains the README for the original code by Sandro Stucki.
-- Note that we have deleted files that were unneeded for our purposes, so not all
--  of the files discussed below are still there..

-- This code has been tested to type-check with Agda 2.6.0.1 and the latest HEAD of agda-stdlib (e0dc14a2)





-- The code in this directory contains an Agda formalization of the
-- Girard-Reynolds polymorphic lambda calculus (System F) extended
-- with iso-recursive types.
--
-- The code makes heavy use of the Agda standard library, which is
-- freely available from
--
--   https://github.com/agda/agda-stdlib/
--
-- The code has been tested using Agda 2.6.0.1 and version 1.0.1 of the
-- Agda standard library.


module README where

------------------------------------------------------------------------
-- Module overview

-- The formalization is organized in the following modules.

-- Syntax for terms and types along with support for term/type
-- substitutions.  These modules also contain church/CPS encodings for
-- some other forms, such as existential types or tuples.
open import SystemF.Term
open import SystemF.Type

-- Typing derivations along with substitution/weakening lemmas.
open import SystemF.WtTerm

-- A (functional) call-by-value small-step semantics.  This module
-- also contains a type soundness proof with respect to to said
-- semantics as well as a proof of its equivalence (strong
-- bisimilarity) to the big-step semantics mentioned below.  The type
-- soundness proof uses the common progress & preservation
-- (i.e. subject reduction) structure.
open import SystemF.Reduction

-- Two equivalent versions of a (functional) call-by-value big-step
-- semantics along with corresponding type soundness proofs.  The
-- second version is formulated without the use of productivity
-- checker workarounds.  The latter module also contains an
-- equivalence proof of the two semantics.
open import SystemF.Eval
open import SystemF.Eval.NoWorkarounds

-- Decision procedures for type checking and a uniqueness proof for
-- typing derivations.
open import SystemF.TypeCheck

-- Danielsson's partiality-and-failure monad.  This monad provides the
-- domain in which functional operational semantics are formulated.
open import PartialityAndFailure
