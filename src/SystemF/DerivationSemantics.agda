module SystemF.DerivationSemantics where

open import Data.Nat using (suc; zero)
open import Data.Vec using (_∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.All as MaybeAll
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import SystemF.WtTerm
open import SystemF.Term
open import SystemF.Type
open import SystemF.ReductionJudgement

open TypeSubst using () renaming (_[/_]  to _[/tp_])
open CtxSubst  using () renaming (weaken to weakenCtx)

open TermTypeSubst   using () renaming (_/_ to _/tp_; _[/_]  to _[/tmTp_])
open TermTermSubst   using () renaming (_/_ to _/tm_; _[/_]  to _[/tmTm_])
open WtTermTypeSubst using () renaming (_[/_]′ to _[/⊢tmTp_])
open WtTermTermSubst using () renaming (_[/_]  to _[/⊢tmTm_])

data MaybeAllAll {a p q} {A : Set a} {P : A → Set p} (Q : {a : A} → P a → Set q) :
                 {v : Maybe A} → All P v → Set q where
     just : ∀ {v} {pv : P v} → Q pv → MaybeAllAll Q (just pv)
     nothing : MaybeAllAll Q nothing


data ValueDeriv {s} {Γ : Ctx 0 0} : ∀ {t : Term 0 0} {τ : Type 0} → [ s ] Γ ⊢ t ∈ τ → Set where
  λ' : ∀ {t b a} (ty : [ s ] a ∷ Γ ⊢ t ∈ b) → ValueDeriv (λ' a ty)
  Λ : ∀ {t a} (ty : [ s ] weakenCtx Γ ⊢ t ∈ a) → ValueDeriv (Λ ty)
  fold : ∀ {t a} {ty : [ s ] Γ ⊢ t ∈ a [/tp μ a ]} → ValueDeriv ty → ValueDeriv (fold a ty)
  pack : ∀ {t b a} {ty : [ s ] Γ ⊢ t ∈ b [/tp a ]} → ValueDeriv ty → ValueDeriv (pack {τ₁ = b} a ty)

normalizeDeriv : ∀ {s} {v : Val 0 0} {τ} → [ s ] [] ⊢ ⌜ v ⌝ ∈ τ → [ s ] [] ⊢ ⌜ v ⌝ ∈ τ
normalizeDeriv-Value : ∀ {s} {v : Val 0 0} {τ} → (ty : [ s ] [] ⊢ ⌜ v ⌝ ∈ τ) →
                       ValueDeriv (normalizeDeriv ty)
normalizeDeriv {iso} {Λ x} (Λ ty) = Λ ty
normalizeDeriv {iso} {λ' x t} (λ' .x ty) = λ' x ty
normalizeDeriv {iso} {pack τ v} (pack τ ty) = pack τ (normalizeDeriv ty)
normalizeDeriv {iso} {fold a v} (fold a ty) = fold a (normalizeDeriv ty)
normalizeDeriv {equi} {Λ x} (Λ ty) = Λ ty
normalizeDeriv {equi} {λ' x t} (λ' .x ty) = λ' x ty
normalizeDeriv {equi} {pack τ v} (pack τ ty) = pack τ (normalizeDeriv ty)
normalizeDeriv {equi} {v} (fold a ty) = fold a (normalizeDeriv ty)
normalizeDeriv {equi} {v} (unfold a ty) with normalizeDeriv ty | normalizeDeriv-Value ty
normalizeDeriv {equi} {v} (unfold a ty) | fold a ty′ | fold tyV′ = ty′

normalizeDeriv-Value {iso} {Λ x} (Λ ty) = Λ ty
normalizeDeriv-Value {iso} {λ' a t} (λ' a ty) = λ' ty
normalizeDeriv-Value {iso} {pack τ v} (pack τ ty) = pack (normalizeDeriv-Value ty)
normalizeDeriv-Value {iso} {fold x v} (fold x ty) = fold (normalizeDeriv-Value ty)
normalizeDeriv-Value {equi} {Λ x} (Λ ty) = Λ ty
normalizeDeriv-Value {equi} {λ' a x₁} (λ' a ty) = λ' ty
normalizeDeriv-Value {equi} {Λ x} (fold a ty) = fold (normalizeDeriv-Value ty)
normalizeDeriv-Value {equi} {λ' x x₁} (fold a ty) = fold (normalizeDeriv-Value ty)
normalizeDeriv-Value {equi} {pack τ v} (fold a ty) = fold (normalizeDeriv-Value ty)
normalizeDeriv-Value {equi} {pack τ v} (pack τ ty) = pack (normalizeDeriv-Value ty)
normalizeDeriv-Value {equi} {fold x v} (fold a ty) = fold (normalizeDeriv-Value ty)
normalizeDeriv-Value {equi} {Λ x} (unfold a ty) with normalizeDeriv ty | normalizeDeriv-Value ty
normalizeDeriv-Value {equi} {Λ x} (unfold a ty) | fold a ty₁ | fold tyV′ = tyV′
normalizeDeriv-Value {equi} {λ' x x₁} (unfold a ty) with normalizeDeriv ty | normalizeDeriv-Value ty
normalizeDeriv-Value {equi} {λ' x x₁} (unfold a ty) | fold a ty₁ | fold tyV′ = tyV′
normalizeDeriv-Value {equi} {pack τ v} (unfold a ty) with normalizeDeriv ty | normalizeDeriv-Value ty
normalizeDeriv-Value {equi} {pack τ v} (unfold a ty) | fold a ty₁ | fold tyV′ = tyV′
normalizeDeriv-Value {equi} {fold x v} (unfold a ty) with normalizeDeriv ty | normalizeDeriv-Value ty
normalizeDeriv-Value {equi} {fold x v} (unfold a ty) | fold a ty₁ | fold tyV′ = tyV′


preservation : ∀ {s τ t₁ t₂} (ty : [ s ] [] ⊢ t₁ ∈ τ) →
               t₁ ⟶t t₂ →
               [ s ] [] ⊢ t₂ ∈ τ
preservation (ty [ b ]) (App eval) = preservation ty eval [ b ]
preservation (ty [ b ]) Beta with normalizeDeriv ty | normalizeDeriv-Value ty
preservation (ty [ b ]) Beta | .(Λ ty₁) | Λ ty₁ = ty₁ [/⊢tmTp b ]
preservation (ty₁ · ty₂) (app₁ eval) = preservation ty₁ eval · ty₂
preservation (ty₁ · ty₂) (app₂ eval) = normalizeDeriv ty₁ · preservation ty₂ eval
preservation (ty₁ · ty₂) beta with normalizeDeriv ty₁ | normalizeDeriv-Value ty₁ | normalizeDeriv ty₂ | normalizeDeriv-Value ty₂
preservation (ty₁ · ty₂) beta | .(λ' _ ty₁′) | λ' ty₁′ | ty₂′ | vty₂′ = ty₁′ [/⊢tmTm ty₂′ ]
preservation (unpack ty₁ ty₂) (unpack eval) = unpack (preservation ty₁ eval) ty₂
preservation (pack τ ty) (pack eval) = pack τ (preservation ty eval)
preservation (unpack ty₁ ty₂) unpackPack with normalizeDeriv ty₁ | normalizeDeriv-Value ty₁
preservation {s} {τ₂} {t₁} {t₂} (unpack {τ₁ = τ₁} {τ₂ = τ₂} ty₁ ty₂) (unpackPack {v = v}) | pack τ ty | pack tyV =
  ⊢substTp (TypeLemmas.weaken-sub′ τ₂) ((ty₂ WtTermTypeSubst.[/ τ ]) [/⊢tmTm ty ])
preservation {s = iso} (fold a ty) (fold eval) = fold a (preservation ty eval)
preservation {iso} (unfold a ty) (unfold eval) = unfold a (preservation ty eval)
preservation {iso} (unfold a (fold .a ty)) unfoldFold = ty
preservation {s = equi} (fold a ty) eval = fold a (preservation ty eval)
preservation {s = equi} (unfold a ty) eval = unfold a (preservation ty eval)

preservation* : ∀ {s τ t₁ t₂} (ty : [ s ] [] ⊢ t₁ ∈ τ) →
               t₁ ⟶t* t₂ →
               [ s ] [] ⊢ t₂ ∈ τ
preservation* ty refl⟶t* = ty
preservation* ty (underlying⟶t* eval) = preservation ty eval
preservation* ty (trans⟶t* evals₁ evals₂) = preservation* (preservation* ty evals₁) evals₂

