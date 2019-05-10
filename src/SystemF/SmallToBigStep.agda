module SystemF.SmallToBigStep where

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
open import SystemF.Reduction
open import SystemF.Eval hiding (type-soundness)

open TypeSubst       using () renaming (_[/_]  to _[/tp_])
open TermTypeSubst   using () renaming (_[/_]  to _[/tmTp_])
open TermTermSubst   using () renaming (_[/_]  to _[/tmTm_])
open WtTermTypeSubst using () renaming (_[/_]′ to _[/⊢tmTp_])
open WtTermTermSubst using () renaming (_[/_]  to _[/⊢tmTm_])


infix 7 _↓ ⊢_↓

-- Evaluation of untyped (open) terms in the partiality monad via
-- repeated reduction.
_↓ : ∀ {m n} → Term m n → Comp m n
t ↓ with step t
... | just (continue t′) = later (♯ (t′ ↓))
... | just (done v)      = return v
... | nothing            = fail

-- Evaluation of closed terms preserves well-typedness.
⊢_↓ : ∀ {s t a} → [ s ] [] ⊢ t ∈ a → [ s ] [] ⊢comp t ↓ ∈ a
⊢_↓ {t = t} ⊢t with step t | ⊢step ⊢t | progress ⊢t
... | just (continue t′) | just (⊢continue ⊢t′) | just tt = later (♯ ⊢ ⊢t′ ↓)
... | just (done v)      | just (⊢done ⊢v)      | just tt = now (just ⊢v)
... | nothing            | _                    | ()

-- Type soundness: evaluation of well-typed terms does not fail.
type-soundness : ∀ {s t a} → [ s ] [] ⊢ t ∈ a → ¬ t ↓ ≈ fail
type-soundness ⊢t = does-not-fail ⊢ ⊢t ↓


----------------------------------------------------------------------
-- Strong bisimilarity of big-step and small-step semantics

open PF.AlternativeEquality
  renaming (return to returnP; fail to failP; _>>=_ to _>>=P_)

-- Lemma: _↓ "preserves" values.
↓-val : ∀ {m n} (v : Val m n) → ⌜ v ⌝ ↓ ≡ return v
↓-val v with step ⌜ v ⌝ | step-val v
↓-val v | just (continue t) | ()
↓-val v | just (done w) | w≡v = P.cong toComp w≡v
  where toComp : ∀ {m n} → Maybe (Result m n) → Comp m n
        toComp (just (continue t′)) = later (♯ (t′ ↓))
        toComp (just (done v))      = return v
        toComp nothing              = fail
↓-val v | nothing | ()

mutual
  infix 7 _[_]⇓≅↓′ _·⇓≅↓′_

  -- A helper lemma relating reduction and evaluation of type
  -- application.
  _[_]⇓≅↓′ : ∀ {m n} (t : Term m n) (a : Type n) →
             (t ↓) [ a ]⇓ ≅P (t [ a ]) ↓
  t [ a ]⇓≅↓′ with step t
  ... | just (continue t′)     = later (♯ (t′ [ a ]⇓≅↓′))
  ... | just (done (Λ t′))     = later (♯ ⇓≅↓′ (t′ [/tmTp a ]) )
  ... | just (done (λ' _ _))   = failP
  ... | just (done (fold _ _)) = failP
  ... | nothing                = failP

  -- A helper lemma relating reduction and evaluation of term
  -- application.
  _·⇓≅↓′_ : ∀ {m n} (s : Term m n) (t : Term m n) →
            (s ↓) ·⇓ (t ↓) ≅P (s · t) ↓
  s ·⇓≅↓′ t with step s
  s ·⇓≅↓′ t | just (continue s′)     = later (♯ (s′ ·⇓≅↓′ t))
  s ·⇓≅↓′ t | just (done v)          with step t
  s ·⇓≅↓′ t | just (done v)          | just (continue t′) = later (♯ subst v)
    where
      subst : ∀ v → (return v) ·⇓ (t′ ↓) ≅P (⌜ v ⌝ · t′) ↓
      subst v with ⌜ v ⌝ ↓ | ↓-val v | ⌜ v ⌝ ·⇓≅↓′ t′
      subst v | now (just .v) | P.refl | v≅t′ = v≅t′
      subst _ | now nothing   | ()     | _
      subst _ | later x₁      | ()     | _
  s ·⇓≅↓′ t | just (done (Λ s′))     | just (done w) = failP
  s ·⇓≅↓′ t | just (done (λ' a s′))  | just (done w) =
    later (♯ ⇓≅↓′ (s′ [/tmTm ⌜ w ⌝ ]))
  s ·⇓≅↓′ t | just (done (fold x v)) | just (done w) = failP
  s ·⇓≅↓′ t | just (done v)          | nothing       = failP
  s ·⇓≅↓′ t | nothing                                = failP

  -- A helper lemma relating reduction and evaluation of recursive
  -- type folding.
  fold⇓≅↓′ : ∀ {m n} (a : Type (1 + n)) (t : Term m n) →
             fold⇓ a (t ↓) ≅P (fold a t) ↓
  fold⇓≅↓′ a t with step t
  ... | just (continue t′) = later (♯ fold⇓≅↓′ a t′)
  ... | just (done v)      = returnP P.refl
  ... | nothing            = failP

  -- A helper lemma relating reduction and evaluation of recursive
  -- type unfolding.
  unfold⇓≅↓′ : ∀ {m n} (a : Type (1 + n)) (t : Term m n) →
               unfold⇓ a (t ↓) ≅P (unfold a t) ↓
  unfold⇓≅↓′ a t with step t
  ... | just (continue t′) = later (♯ unfold⇓≅↓′ a t′)
  ... | just (done (Λ _))      = failP
  ... | just (done (λ' _ _))   = failP
  ... | just (done (fold _ v)) = returnP P.refl
  ... | nothing                = failP

  -- Big-step evaluation and small-step reduction are strongly bisimliar.
  ⇓≅↓′ : ∀ {m n} (t : Term m n) → t ⇓ ≅P t ↓
  ⇓≅↓′ (var x)        = failP
  ⇓≅↓′ (Λ t)          = returnP P.refl
  ⇓≅↓′ (λ' a t)       = returnP P.refl
  ⇓≅↓′ (μ a t)        = later (♯ ⇓≅↓′ (t [/tmTm μ a t ]))
  ⇓≅↓′ (t [ a ])      =
    (t [ a ]) ⇓       ≅⟨ complete ([]-comp t a) ⟩
    (t ⇓) [ a ]⇓      ≅⟨ (⇓≅↓′ t) >>=P (λ v → (_ ∎)) ⟩
    (t ↓) [ a ]⇓      ≅⟨ t [ a ]⇓≅↓′ ⟩
    (t [ a ]) ↓       ∎
  ⇓≅↓′ (s · t)        =
    (s · t) ⇓         ≅⟨ complete (·-comp s t) ⟩
    (s ⇓) ·⇓ (t ⇓)    ≅⟨ (⇓≅↓′ s >>=P λ v → ⇓≅↓′ t >>=P λ w → (_ ∎)) ⟩
    (s ↓) ·⇓ (t ↓)    ≅⟨ s ·⇓≅↓′ t ⟩
    (s · t) ↓         ∎
  ⇓≅↓′ (fold a t)     =
    (fold a t) ⇓      ≅⟨ complete (fold-comp a t) ⟩
    fold⇓ a (t ⇓)     ≅⟨ (⇓≅↓′ t) >>=P (λ v → (_ ∎)) ⟩
    fold⇓ a (t ↓)     ≅⟨ fold⇓≅↓′ a t ⟩
    (fold a t) ↓      ∎
  ⇓≅↓′ (unfold a t)   =
    (unfold a t) ⇓    ≅⟨ complete (unfold-comp a t) ⟩
    unfold⇓ a (t ⇓)   ≅⟨ (⇓≅↓′ t) >>=P (λ v → (_ ∎)) ⟩
    unfold⇓ a (t ↓)   ≅⟨ unfold⇓≅↓′ a t ⟩
    (unfold a t) ↓    ∎

-- Big-step evaluation and small-step reduction are strongly bisimliar.
⇓≅↓ : ∀ {m n} (t : Term m n) → t ⇓ ≅ t ↓
⇓≅↓ t = sound (⇓≅↓′ t)
