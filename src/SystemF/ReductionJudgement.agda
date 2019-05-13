module SystemF.ReductionJudgement where

open import SystemF.Term
open import SystemF.Type
open import SystemF.WtTerm

open TypeSubst       using () renaming (_[/_]  to _[/tp_])
open TermTypeSubst   using () renaming (_[/_]  to _[/tmTp_])
open TermTermSubst   using () renaming (_[/_]  to _[/tmTm_])
open WtTermTypeSubst using () renaming (_[/_]′ to _[/⊢tmTp_])
open WtTermTermSubst using () renaming (_[/_]  to _[/⊢tmTm_])

data _⟶t_ : Term 0 0 → Term 0 0 → Set where
  App : ∀ {t₁ t₂ a} → t₁ ⟶t t₂ → (t₁ [ a ]) ⟶t (t₂ [ a ])
  Beta : ∀ {t a} → ((Λ t) [ a ]) ⟶t (t [/tmTp a ])
  app₁ : ∀ {t₁ t₁′ t₂} → t₁ ⟶t t₁′ → (t₁ · t₂) ⟶t (t₁′ · t₂)
  app₂ : ∀ {v₁ t₂ t₂′} → t₂ ⟶t t₂′ → (⌜ v₁ ⌝ · t₂) ⟶t (⌜ v₁ ⌝ · t₂′)
  beta : ∀ {t₁ v₂ a} → ((λ' a t₁) · ⌜ v₂ ⌝) ⟶t (t₁ [/tmTm ⌜ v₂ ⌝ ])
  fold : ∀ {t t′ a} → t ⟶t t′ → fold a t ⟶t fold a t′
  unfold : ∀ {t t′ a} → t ⟶t t′ → unfold a t ⟶t unfold a t′
  unfoldFold : ∀ {v a a′} → unfold a (fold a′ ⌜ v ⌝) ⟶t ⌜ v ⌝

data _⟶t*_ (t₁ : Term 0 0) : Term 0 0 → Set where
  refl⟶t* : t₁ ⟶t* t₁
  underlying⟶t* : ∀ {t₂} → t₁ ⟶t t₂ → t₁ ⟶t* t₂
  trans⟶t* : ∀ {t₂ t₃} → t₁ ⟶t* t₂ → t₂ ⟶t* t₃ → t₁ ⟶t* t₃

App⟶t* : ∀ {t₁ t₂ a} → t₁ ⟶t* t₂ → (t₁ [ a ]) ⟶t* (t₂ [ a ])
App⟶t* refl⟶t* = refl⟶t*
App⟶t* (underlying⟶t* eval) = underlying⟶t* (App eval)
App⟶t* (trans⟶t* evals₁ evals₂) = trans⟶t* (App⟶t* evals₁) (App⟶t* evals₂)

app₁⟶t* : ∀ {t₁ t₁′ t₂} → t₁ ⟶t* t₁′ → (t₁ · t₂) ⟶t* (t₁′ · t₂)
app₁⟶t* refl⟶t* = refl⟶t*
app₁⟶t* (underlying⟶t* eval) = underlying⟶t* (app₁ eval)
app₁⟶t* (trans⟶t* evals₁ evals₂) = trans⟶t* (app₁⟶t* evals₁) (app₁⟶t* evals₂)

app₂⟶t* : ∀ {v₁ t₂ t₂′} → t₂ ⟶t* t₂′ → (⌜ v₁ ⌝ · t₂) ⟶t* (⌜ v₁ ⌝ · t₂′)
app₂⟶t* refl⟶t* = refl⟶t*
app₂⟶t* (underlying⟶t* eval) = underlying⟶t* (app₂ eval)
app₂⟶t* (trans⟶t* evals₁ evals₂) = trans⟶t* (app₂⟶t* evals₁) (app₂⟶t* evals₂)

data _⇓ (t : Term 0 0) : Set where
  term : ∀ v → t ⟶t* ⌜ v ⌝ → t ⇓

