----------------------------------------------------------------------
-- Functional small-step semantics
----------------------------------------------------------------------

module SystemF.Reduction where

open import Codata.Musical.Notation
open import Category.Monad
open import Category.Monad.Partiality.All
open import Data.Maybe as Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Relation.Unary.All as MaybeAll using (nothing; just)
open import Data.Maybe.Relation.Unary.Any as MaybeAny using (just)
open import Data.Nat using (ℕ; _+_)
open import Data.Unit using (tt)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)
open import Relation.Nullary

open import PartialityAndFailure as PF
open PF.Equality hiding (fail)
open PF.Equivalence
private
  open module M {f} = RawMonad (PF.monad {f}) using (_>>=_; return)

open import SystemF.Type
open import SystemF.Term
open import SystemF.WtTerm
-- open import SystemF.Eval hiding (type-soundness)

open TypeSubst       using () renaming (_[/_]  to _[/tp_])
open TermTypeSubst   using () renaming (_[/_]  to _[/tmTp_])
open TermTermSubst   using () renaming (_[/_]  to _[/tmTm_])
open WtTermTypeSubst using () renaming (_[/_]′ to _[/⊢tmTp_])
open WtTermTermSubst using () renaming (_[/_]  to _[/⊢tmTm_])

----------------------------------------------------------------------
-- Functional call-by-value small-step semantics in the partiality
-- monad

-- The functional presentation of the small-step semantics below is
-- heavily inspired by Danielsson's ICFP'12 paper "Operational
-- Semantics Using the Partiality Monad".  Whereas the paper
-- illustrates the technique to give a functional abstract machine
-- semantics (i.e. the semantics of a "VM"), we skip the compilation
-- step and directly reduce terms, which results in a (functional)
-- structural operational semantics (SOS).  We adopt many of the
-- conventions used in the accompanying code, which can be found at
--
--   http://www.cse.chalmers.se/~nad/publications/danielsson-semantics-partiality-monad.tgz
--
-- As pointed out in Danielsson's paper, the functional presentation
-- of the semantics feels rather natural in that it follows the form
-- of an interpreter, and it has the added advantage of proving that
-- the semantics are deterministic and computable "for free".
--
-- For more information about Danielson's paper see
--
--   http://www.cse.chalmers.se/~nad/publications/danielsson-semantics-partiality-monad.html


----------------------------------------------------------------------
-- Small-step call-by-value reduction

-- Results of reduction steps
data Result (m n : ℕ) : Set where
  continue : (t : Term m n) → Result m n  -- further reducible term
  done     : (v : Val m n)  → Result m n  -- irreducible value

-- Take a single reduction step (if possible).
step : ∀ {m n} → Term m n → Maybe (Result m n)
step (var x)                 = nothing
step (Λ t)                   = just (done (Λ t))
step (λ' a t)                = just (done (λ' a t))
step (μ a t)                 = just (continue (t [/tmTm μ a t ]))
step (t [ a ])               with step t
... | just (continue t′)     = just (continue (t′ [ a ]))
... | just (done (Λ t′))     = just (continue (t′ [/tmTp a ]))
... | just (done _)          = nothing
... | nothing                = nothing
step {m} {n} (s · t)         with step s
... | just (continue s′)     = just (continue (s′ · t))
... | just (done v)          = nested v
  where -- Call-by-value: only reduce (s · t) if s is a value.
    nested : Val m n → Maybe (Result m n)
    nested v with step t
    nested v         | (just (continue t′)) = just (continue (⌜ v ⌝ · t′))
    nested (λ' _ s′) | (just (done v)) = just (continue (s′ [/tmTm ⌜ v ⌝ ]))
    nested _         | (just (done _)) = nothing
    nested _         | nothing         = nothing
... | nothing                = nothing
step (fold a t)              with step t
... | just (continue t′)     = just (continue (fold a t′))
... | just (done v)          = just (done (fold a v))
... | nothing                = nothing
step (unfold a t)            with step t
... | just (continue t′)     = just (continue (unfold a t′))
... | just (done (fold _ v)) = just (done v)
... | just (done _)          = nothing
... | nothing                = nothing


----------------------------------------------------------------------
-- Type soundness

infix 4 [_]_⊢res_∈_ [_]_⊢res?_∈_

-- Well-typedness lifted to results of reduction steps.
data [_]_⊢res_∈_ (s : Style) {m n} (Γ : Ctx m n) : Result m n → Type n → Set where
  ⊢continue : ∀ {t a} → [ s ] Γ ⊢    t ∈ a → [ s ] Γ ⊢res continue t ∈ a
  ⊢done     : ∀ {v a} → [ s ] Γ ⊢val v ∈ a → [ s ] Γ ⊢res done v     ∈ a

-- Well-typedness lifted to possibly undefined reduction steps.
[_]_⊢res?_∈_ : ∀ (s : Style) {m n} → Ctx m n → Maybe (Result m n) → Type n → Set
[ s ] Γ ⊢res? r? ∈ a = MaybeAll.All (λ r → [ s ] Γ ⊢res r ∈ a) r?

-- Preservation of well-typedness: a well-typed term reduces in one
-- step to a result of the same type or fails to reduce.
⊢step : ∀ {s m n} {Γ : Ctx m n} {t a} → [ s ] Γ ⊢ t ∈ a → [ s ] Γ ⊢res? step t ∈ a
⊢step (var x)   = nothing
⊢step (Λ ⊢t)    = just (⊢done (Λ ⊢t))
⊢step (λ' a ⊢t) = just (⊢done (λ' a ⊢t))
-- ⊢step (μ a ⊢t)  = just (⊢continue (⊢t [/⊢tmTm μ a ⊢t ]))
⊢step {t = t [ a ]} (⊢t [ .a ]) with step t | ⊢step ⊢t
... | just ._ | just (⊢continue ⊢t′) = just (⊢continue (⊢t′ [ a ]))
... | just ._ | just (⊢done (Λ ⊢t′)) = just (⊢continue (⊢t′ [/⊢tmTp a ]))
... | nothing | nothing              = nothing
⊢step {s} {m} {n} {Γ} {t₁ · t₂} {b} (⊢t₁ · ⊢t₂) with step t₁ | ⊢step ⊢t₁
... | just ._ | just (⊢continue ⊢t₁′) = just (⊢continue (⊢t₁′ · ⊢t₂))
... | just (done (λ' a t₁′)) | just (⊢done (λ' .a ⊢t₁′)) = nested
  where
    nested : [ s ] Γ ⊢res? step ((λ' a t₁′) · t₂) ∈ b
    nested with step t₂ | ⊢step ⊢t₂
    ... | just ._ | just (⊢continue ⊢t₂′) = just (⊢continue ((λ' a ⊢t₁′) · ⊢t₂′))
    ... | just ._ | just (⊢done v) = just (⊢continue (⊢t₁′ [/⊢tmTm ⊢⌜ v ⌝ ]))
    ... | nothing | nothing        = nothing
... | nothing | nothing = nothing
⊢step {s = iso} {t = fold a t} (fold .a ⊢t) with step t | ⊢step ⊢t
... | just ._ | just (⊢continue ⊢t′) = just (⊢continue (fold a ⊢t′))
... | just ._ | just (⊢done ⊢v)      = just (⊢done (fold a ⊢v))
... | nothing | nothing              = nothing
⊢step {s = equi} {t = t} (fold a ⊢t) with step t | ⊢step ⊢t
... | just ._ | just (⊢continue ⊢t′) = just (⊢continue (fold a ⊢t′))
... | just ._ | just (⊢done ⊢v)      = just (⊢done (fold a ⊢v))
... | nothing | nothing              = nothing
⊢step {s = iso} {t = unfold a t} (unfold .a ⊢t) with step t | ⊢step ⊢t
... | just ._ | just (⊢continue ⊢t′)      = just (⊢continue (unfold a ⊢t′))
... | just ._ | just (⊢done (fold .a ⊢v)) = just (⊢done ⊢v)
... | nothing | nothing                   = nothing
⊢step {s = equi} {t = t} (unfold a ⊢t) with step t | ⊢step ⊢t
... | just ._ | just (⊢continue ⊢t′)      = just (⊢continue (unfold a ⊢t′))
... | just ._ | just (⊢done (fold .a ⊢v)) = just (⊢done ⊢v)
... | nothing | nothing                   = nothing

-- Progress: reduction of well-typed closed terms does not fail.
progress : ∀ {s t} {a : Type 0} → [ s ] [] ⊢ t ∈ a → Maybe.Is-just (step t)
progress (var ())
progress (Λ t) = just tt
progress (λ' a t) = just tt
-- progress (μ a t) = just tt
progress {t = t [ a ]} (⊢t [ .a ]) with step t | ⊢step ⊢t | progress ⊢t
... | just ._ | just (⊢continue _) | just tt = just tt
... | just ._ | just (⊢done (Λ _)) | just tt = just tt
progress {t = s · t} (⊢s · ⊢t) with step s | ⊢step ⊢s | progress ⊢s
... | just ._               | just (⊢continue _)     | just tt = just tt
... | just (done (λ' a s′)) | just (⊢done (λ' .a _)) | just tt = nested
  where
    nested : Maybe.Is-just (step ((λ' a s′) · t))
    nested with step t | ⊢step ⊢t | progress ⊢t
    ... | just ._ | just (⊢continue _) | just tt = just tt
    ... | just ._ | just (⊢done _)     | just tt = just tt
progress {s = iso} {t = fold a t} (fold .a ⊢t) with step t | ⊢step ⊢t | progress ⊢t
... | just ._ | just (⊢continue _) | just tt = just tt
... | just ._ | just (⊢done _)     | just tt = just tt
progress {s = equi} {t = t} (fold a ⊢t) with step t | ⊢step ⊢t | progress ⊢t
... | just ._ | just (⊢continue _) | just tt = just tt
... | just ._ | just (⊢done _)     | just tt = just tt
progress {s = iso} {t = unfold a t} (unfold .a ⊢t) with step t | ⊢step ⊢t | progress ⊢t
... | just ._ | just (⊢continue _)       | just tt = just tt
... | just ._ | just (⊢done (fold .a _)) | just tt = just tt
progress {s = equi} {t = t} (unfold a ⊢t) with step t | ⊢step ⊢t | progress ⊢t
... | just ._ | just (⊢continue _)       | just tt = just tt
... | just ._ | just (⊢done (fold .a _)) | just tt = just tt
