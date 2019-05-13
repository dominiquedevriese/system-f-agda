module SystemF.Contexts where

open import Data.Vec using ([]; _∷_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function.Equivalence using (_⇔_)

open import SystemF.Term
open import SystemF.Type
open import SystemF.WtTerm
open import SystemF.ReductionJudgement

open TypeSubst using () renaming (_[/_]  to _[/tp_])
open CtxSubst  using () renaming (weaken to weakenCtx)

data Context (mᵢ nᵢ : ℕ) : (mₒ nₒ : ℕ) → Set where
  hole    : Context mᵢ nᵢ mᵢ nᵢ
  Λ       : ∀ {mₒ nₒ} → Context mᵢ nᵢ mₒ (suc nₒ)                  → Context mᵢ nᵢ mₒ nₒ
  λ'      : ∀ {mₒ nₒ} → Type nₒ       → Context mᵢ nᵢ (suc mₒ) nₒ  → Context mᵢ nᵢ mₒ nₒ
  _[_]    : ∀ {mₒ nₒ} → Context mᵢ nᵢ mₒ nₒ     → Type nₒ          → Context mᵢ nᵢ mₒ nₒ
  _·₁_    : ∀ {mₒ nₒ} → Context mᵢ nᵢ mₒ nₒ     → Term mₒ nₒ       → Context mᵢ nᵢ mₒ nₒ
  _·₂_    : ∀ {mₒ nₒ} → Term mₒ nₒ     → Context mᵢ nᵢ mₒ nₒ       → Context mᵢ nᵢ mₒ nₒ
  fold    : ∀ {mₒ nₒ} → Type (suc nₒ) → Context mᵢ nᵢ mₒ nₒ        → Context mᵢ nᵢ mₒ nₒ
  unfold  : ∀ {mₒ nₒ} → Type (suc nₒ) → Context mᵢ nᵢ mₒ nₒ        → Context mᵢ nᵢ mₒ nₒ

plug : ∀ {mᵢ nᵢ mₒ nₒ} → Context mᵢ nᵢ mₒ nₒ → Term mᵢ nᵢ → Term mₒ nₒ
plug hole t = t
plug (Λ ctx) t = Λ (plug ctx t)
plug (λ' a ctx) t = λ' a (plug ctx t)
plug (ctx [ a ]) t = plug ctx t [ a ]
plug (ctx ·₁ t₂) t = plug ctx t · t₂
plug (t₁ ·₂ ctx) t = t₁ · plug ctx t
plug (fold a ctx) t = fold a (plug ctx t)
plug (unfold a ctx) t = unfold a (plug ctx t)

infix  4 [_]⊢_∈_∣_⇒_∣_

foldMaybeC : (s : Style) → ∀ {mᵢ nᵢ mₒ nₒ} → (a : Type (suc nₒ)) → (C : Context mᵢ nᵢ mₒ nₒ) → Context mᵢ nᵢ mₒ nₒ
foldMaybeC iso a t = fold a t
foldMaybeC equi a t = t

unfoldMaybeC : (s : Style) → ∀ {mᵢ nᵢ mₒ nₒ} → (a : Type (suc nₒ)) → (t : Context mᵢ nᵢ mₒ nₒ) → Context mᵢ nᵢ mₒ nₒ
unfoldMaybeC iso a t = unfold a t
unfoldMaybeC equi a t = t

data [_]⊢_∈_∣_⇒_∣_ {mᵢ nᵢ} : ∀ {mₒ nₒ} (s : Style) (C : Context mᵢ nᵢ mₒ nₒ)
                   (Γᵢ : Ctx mᵢ nᵢ) (τᵢ : Type nᵢ) (Γₒ : Ctx mₒ nₒ) (τₒ : Type nₒ) →
                   Set where
     hole : ∀ {s Γᵢ τᵢ} → [ s ]⊢ hole ∈ Γᵢ ∣ τᵢ ⇒ Γᵢ ∣ τᵢ
     Λ : ∀ {s Γᵢ τᵢ mₒ nₒ} {Γₒ : Ctx mₒ nₒ} {τₒ C} →
         [ s ]⊢ C ∈ Γᵢ ∣ τᵢ ⇒ weakenCtx Γₒ ∣ τₒ → [ s ]⊢ Λ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ ∀' τₒ
     λ' : ∀ {s Γᵢ τᵢ mₒ nₒ} {Γₒ : Ctx mₒ nₒ} τₒ₁ {τₒ₂ C} →
         [ s ]⊢ C ∈ Γᵢ ∣ τᵢ ⇒ τₒ₁ ∷ Γₒ ∣ τₒ₂ → [ s ]⊢ λ' τₒ₁ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ (τₒ₁ →' τₒ₂)
     _[_] : ∀ {s Γᵢ τᵢ mₒ nₒ} {Γₒ : Ctx mₒ nₒ} {τₒ₁ C} →
            [ s ]⊢ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ ∀' τₒ₁ →
            (τₒ₂ : Type nₒ) →
            [ s ]⊢ C [ τₒ₂ ] ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ (τₒ₁ [/tp τₒ₂ ])
     _·₁_ : ∀ {s Γᵢ τᵢ mₒ nₒ} {Γₒ : Ctx mₒ nₒ} {τₒ₁ τₒ₂ t₂ C} →
            [ s ]⊢ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ τₒ₁ →' τₒ₂ →
            [ s ] Γₒ ⊢ t₂ ∈ τₒ₁ →
            [ s ]⊢ C ·₁ t₂ ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ τₒ₂
     _·₂_ : ∀ {s Γᵢ τᵢ mₒ nₒ} {Γₒ : Ctx mₒ nₒ} {τₒ₁ τₒ₂ t₁ C} →
            [ s ] Γₒ ⊢ t₁ ∈ τₒ₁ →' τₒ₂ →
            [ s ]⊢ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ τₒ₁ →
            [ s ]⊢ t₁ ·₂ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ τₒ₂
     fold : ∀ {s Γᵢ τᵢ mₒ nₒ} {Γₒ : Ctx mₒ nₒ} τₒ {C} →
            [ s ]⊢ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ τₒ [/tp μ τₒ ] →
            [ s ]⊢ foldMaybeC s τₒ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ μ τₒ
     unfold : ∀ {s Γᵢ τᵢ mₒ nₒ} {Γₒ : Ctx mₒ nₒ} τₒ {C} →
            [ s ]⊢ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ μ τₒ →
            [ s ]⊢ unfoldMaybeC s τₒ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ τₒ [/tp μ τₒ ]

plug-ty : ∀ {s} {mᵢ nᵢ} {mₒ nₒ} {C : Context mᵢ nᵢ mₒ nₒ} {t}
            {Γᵢ : Ctx mᵢ nᵢ} {τᵢ : Type nᵢ} {Γₒ : Ctx mₒ nₒ} {τₒ : Type nₒ} →
            [ s ]⊢ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ τₒ →
            [ s ] Γᵢ ⊢ t ∈ τᵢ →
            [ s ] Γₒ ⊢ plug C t ∈ τₒ
plug-ty hole ty = ty
plug-ty (Λ tyC) ty = Λ (plug-ty tyC ty)
plug-ty (λ' a tyC) ty = λ' a (plug-ty tyC ty)
plug-ty (tyC [ τₒ ]) ty = plug-ty tyC ty [ τₒ ]
plug-ty (tyC ·₁ ty′) ty = plug-ty tyC ty · ty′
plug-ty (ty′ ·₂ tyC) ty = ty′ · plug-ty tyC ty
plug-ty {iso} (fold a tyC) ty = fold a (plug-ty tyC ty)
plug-ty {equi} (fold a tyC) ty = fold a (plug-ty tyC ty)
plug-ty {iso} (unfold a tyC) ty = unfold a (plug-ty tyC ty)
plug-ty {equi} (unfold a tyC) ty = unfold a (plug-ty tyC ty)

ctxEquiv : ∀ {s m n} (Γ : Ctx m n) (t₁ t₂ : Term m n) (τ : Type n) (ty₁ : [ s ] Γ ⊢ t₁ ∈ τ) (ty₂ : [ s ] Γ ⊢ t₂ ∈ τ) → Set
ctxEquiv {s} Γ t₁ t₂ τ ty₁ ty₂ =
  ∀ {C τ′} → [ s ]⊢ C ∈ Γ ∣ τ ⇒ [] ∣ τ′ → (plug C t₁ ⇓) ⇔ (plug C t₂ ⇓)

syntax ctxEquiv {s} Γ t₁ t₂ τ ty₁ ty₂ = [ s ] Γ ⊢ t₁ ∣ ty₁ ≈c t₂ ∣ ty₂ ∶ τ
