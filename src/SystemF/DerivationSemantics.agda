module SystemF.DerivationSemantics where

open import Data.Nat using (suc; zero)
open import Data.Vec using (_∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.All as MaybeAll
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import SystemF.WtTerm
open import SystemF.Term
open import SystemF.Type
open import SystemF.ReductionJudgement

open TypeSubst using () renaming (_[/_]  to _[/tp_])
open CtxSubst  using () renaming (weaken to weakenCtx)

open TermTypeSubst   using () renaming (_[/_]  to _[/tmTp_])
open TermTermSubst   using () renaming (_[/_]  to _[/tmTm_])
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

data _⟶d_ {s} : ∀ {t₁ t₂ : Term 0 0} {τ : Type 0} → [ s ] [] ⊢ t₁ ∈ τ → [ s ] [] ⊢ t₂ ∈ τ → Set where
  beta : ∀ {t₁ t₂ b a} (ty₁ : [ s ] a ∷ [] ⊢ t₁ ∈ b) (ty₂ : [ s ] [] ⊢ t₂ ∈ a) →
         ValueDeriv ty₂ →
         ((λ' a ty₁) · ty₂) ⟶d (ty₁ [/⊢tmTm ty₂ ])
  app₁ : ∀ {t₁ t₁′ t₂ b a} {ty₁ : [ s ] [] ⊢ t₁ ∈ (a →' b)} {ty₁′ : [ s ] [] ⊢ t₁′ ∈ (a →' b)} {ty₂ : [ s ] [] ⊢ t₂ ∈ a} →
         ty₁ ⟶d ty₁′ →
         (ty₁ · ty₂) ⟶d (ty₁′ · ty₂)
  app₂ : ∀ {t₁ t₂′ t₂ b a} {ty₁ : [ s ] [] ⊢ t₁ ∈ (a →' b)} {ty₂ : [ s ] [] ⊢ t₂ ∈ a} {ty₂′ : [ s ] [] ⊢ t₂′ ∈ a} →
         ValueDeriv ty₁ →
         ty₂ ⟶d ty₂′ →
         (ty₁ · ty₂) ⟶d (ty₁ · ty₂′)
  Beta : ∀ {t a} {ty : [ s ] weakenCtx [] ⊢ t ∈ a} {b} →
         ((Λ ty) [ b ]) ⟶d (ty [/⊢tmTp b ])
  App : ∀ {t t′ a} {ty : [ s ] [] ⊢ t ∈ ∀' a} {ty′ : [ s ] [] ⊢ t′ ∈ ∀' a} {b} →
        ty ⟶d ty′ → (ty [ b ]) ⟶d (ty′ [ b ])
  unfoldFold : ∀ {t a} {ty : [ s ] [] ⊢ t ∈ a [/tp μ a ]} →
               ValueDeriv ty →
               unfold a (fold a ty) ⟶d ty
  fold : ∀ {t t′ a} {ty : [ s ] [] ⊢ t ∈ a [/tp μ a ]} {ty′ : [ s ] [] ⊢ t′ ∈ a [/tp μ a ]} →
           ty ⟶d ty′ →
           fold a ty ⟶d fold a ty′
  unfold : ∀ {t t′ a} {ty : [ s ] [] ⊢ t ∈ μ a} {ty′ : [ s ] [] ⊢ t′ ∈ μ a} →
           ty ⟶d ty′ →
           unfold a ty ⟶d unfold a ty′

data _⟶d*_ {s} {τ} {t₁} (ty₁ : [ s ] [] ⊢ t₁ ∈ τ) : ∀ {t₂} (ty₂ : [ s ] [] ⊢ t₂ ∈ τ) → Set where
  refl⟶d* : ty₁ ⟶d* ty₁
  underlying⟶d* : ∀ {t₂} {ty₂ : [ s ] [] ⊢ t₂ ∈ τ} → ty₁ ⟶d ty₂ → ty₁ ⟶d* ty₂
  trans⟶d* : ∀ {t₂ t₃} {ty₂ : [ s ] [] ⊢ t₂ ∈ τ} {ty₃ : [ s ] [] ⊢ t₃ ∈ τ} → ty₁ ⟶d* ty₂ → ty₂ ⟶d* ty₃ → ty₁ ⟶d* ty₃

fold-d* : ∀ {s t t′ a} {ty : [ s ] [] ⊢ t ∈ a [/tp μ a ]} {ty′ : [ s ] [] ⊢ t′ ∈ a [/tp μ a ]} →
          ty ⟶d* ty′ → fold a ty ⟶d* fold a ty′
fold-d* refl⟶d* = refl⟶d*
fold-d* (underlying⟶d* eval) = underlying⟶d* (fold eval)
fold-d* (trans⟶d* eval₁ eval₂) = trans⟶d* (fold-d* eval₁) (fold-d* eval₂)

unfold-d* : ∀ {s t t′ a} {ty : [ s ] [] ⊢ t ∈ μ a} {ty′ : [ s ] [] ⊢ t′ ∈ μ a} →
          ty ⟶d* ty′ → unfold a ty ⟶d* unfold a ty′
unfold-d* refl⟶d* = refl⟶d*
unfold-d* (underlying⟶d* eval) = underlying⟶d* (unfold eval)
unfold-d* (trans⟶d* eval₁ eval₂) = trans⟶d* (unfold-d* eval₁) (unfold-d* eval₂)

App-d* : ∀ {s t t′ τ b} {ty : [ s ] [] ⊢ t ∈ ∀' τ} {ty′ : [ s ] [] ⊢ t′ ∈ ∀' τ} →
          ty ⟶d* ty′ → (ty [ b ]) ⟶d* (ty′ [ b ])
App-d* refl⟶d* = refl⟶d*
App-d* (underlying⟶d* eval) = underlying⟶d* (App eval)
App-d* (trans⟶d* eval₁ eval₂) = trans⟶d* (App-d* eval₁) (App-d* eval₂)

app₁-d* : ∀ {s t₁ t₁′ t₂ b a} {ty₁ : [ s ] [] ⊢ t₁ ∈ (a →' b)} {ty₁′ : [ s ] [] ⊢ t₁′ ∈ (a →' b)} {ty₂ : [ s ] [] ⊢ t₂ ∈ a} →
          ty₁ ⟶d* ty₁′ →
          (ty₁ · ty₂) ⟶d* (ty₁′ · ty₂)
app₁-d* refl⟶d* = refl⟶d*
app₁-d* (underlying⟶d* eval) = underlying⟶d* (app₁ eval)
app₁-d* (trans⟶d* evals₁ evals₂) = trans⟶d* (app₁-d* evals₁) (app₁-d* evals₂)

app₂-d* : ∀ {s t₁ t₂′ t₂ b a} {ty₁ : [ s ] [] ⊢ t₁ ∈ (a →' b)} {ty₂ : [ s ] [] ⊢ t₂ ∈ a} {ty₂′ : [ s ] [] ⊢ t₂′ ∈ a} →
          ValueDeriv ty₁ →
          ty₂ ⟶d* ty₂′ →
          (ty₁ · ty₂) ⟶d* (ty₁ · ty₂′)
app₂-d* val refl⟶d* = refl⟶d*
app₂-d* val (underlying⟶d* eval) = underlying⟶d* (app₂ val eval)
app₂-d* val (trans⟶d* evals₁ evals₂) = trans⟶d* (app₂-d* val evals₁) (app₂-d* val evals₂)

normalizeDeriv : ∀ {s} {v : Val 0 0} {τ} → [ s ] [] ⊢ ⌜ v ⌝ ∈ τ → [ s ] [] ⊢ ⌜ v ⌝ ∈ τ
normalizeDeriv-Value : ∀ {s} {v : Val 0 0} {τ} → (ty : [ s ] [] ⊢ ⌜ v ⌝ ∈ τ) →
                       ValueDeriv (normalizeDeriv ty)
normalizeDeriv {iso} {Λ x} (Λ ty) = Λ ty
normalizeDeriv {iso} {λ' x t} (λ' .x ty) = λ' x ty
normalizeDeriv {iso} {fold a v} (fold a ty) = fold a (normalizeDeriv ty)
normalizeDeriv {equi} {Λ x} (Λ ty) = Λ ty
normalizeDeriv {equi} {λ' x t} (λ' .x ty) = λ' x ty
normalizeDeriv {equi} {v} (fold a ty) = fold a (normalizeDeriv ty)
normalizeDeriv {equi} {v} (unfold a ty) with normalizeDeriv ty | normalizeDeriv-Value ty
normalizeDeriv {equi} {v} (unfold a ty) | fold a ty′ | fold tyV′ = ty′

normalizeDeriv-Value {iso} {Λ x} (Λ ty) = Λ ty
normalizeDeriv-Value {iso} {λ' a t} (λ' a ty) = λ' ty
normalizeDeriv-Value {iso} {fold x v} (fold x ty) = fold (normalizeDeriv-Value ty)
normalizeDeriv-Value {equi} {Λ x} (Λ ty) = Λ ty
normalizeDeriv-Value {equi} {λ' a x₁} (λ' a ty) = λ' ty
normalizeDeriv-Value {equi} {Λ x} (fold a ty) = fold (normalizeDeriv-Value ty)
normalizeDeriv-Value {equi} {λ' x x₁} (fold a ty) = fold (normalizeDeriv-Value ty)
normalizeDeriv-Value {equi} {fold x v} (fold a ty) = fold (normalizeDeriv-Value ty)
normalizeDeriv-Value {equi} {Λ x} (unfold a ty) with normalizeDeriv ty | normalizeDeriv-Value ty
normalizeDeriv-Value {equi} {Λ x} (unfold a ty) | fold a ty₁ | fold tyV′ = tyV′
normalizeDeriv-Value {equi} {λ' x x₁} (unfold a ty) with normalizeDeriv ty | normalizeDeriv-Value ty
normalizeDeriv-Value {equi} {λ' x x₁} (unfold a ty) | fold a ty₁ | fold tyV′ = tyV′
normalizeDeriv-Value {equi} {fold x v} (unfold a ty) with normalizeDeriv ty | normalizeDeriv-Value ty
normalizeDeriv-Value {equi} {fold x v} (unfold a ty) | fold a ty₁ | fold tyV′ = tyV′


normalizeDeriv-eval* : ∀ {s} {v : Val 0 0} {τ} → (ty : [ s ] [] ⊢ ⌜ v ⌝ ∈ τ) →
                         ty ⟶d* (normalizeDeriv ty)
normalizeDeriv-eval* {iso} {Λ x} (Λ ty) = refl⟶d*
normalizeDeriv-eval* {equi} {Λ x} (Λ ty) = refl⟶d*
normalizeDeriv-eval* {iso} {λ' a t} (λ' .a ty) = refl⟶d*
normalizeDeriv-eval* {equi} {λ' x x₁} (λ' .x ty) = refl⟶d*
normalizeDeriv-eval* {iso} {fold x v} (fold .x ty) = fold-d* (normalizeDeriv-eval* ty)
normalizeDeriv-eval* {equi} {Λ x} (fold a ty) = fold-d* (normalizeDeriv-eval* ty)
normalizeDeriv-eval* {equi} {λ' x x₁} (fold a ty) = fold-d* (normalizeDeriv-eval* ty)
normalizeDeriv-eval* {equi} {fold x v} (fold a ty) = fold-d* (normalizeDeriv-eval* ty)
normalizeDeriv-eval* {equi} {Λ x} (unfold a ty) with normalizeDeriv ty | normalizeDeriv-Value ty | normalizeDeriv-eval* ty
normalizeDeriv-eval* {equi} {Λ x} (unfold a ty) | fold a ty₁ | fold tyV′ | evals = trans⟶d* (unfold-d* evals) (underlying⟶d* (unfoldFold tyV′))
normalizeDeriv-eval* {equi} {λ' x x₁} (unfold a ty) with normalizeDeriv ty | normalizeDeriv-Value ty | normalizeDeriv-eval* ty
normalizeDeriv-eval* {equi} {λ' x x₁} (unfold a ty) | fold a ty₁ | fold tyV′ | evals = trans⟶d* (unfold-d* evals) (underlying⟶d* (unfoldFold tyV′))
normalizeDeriv-eval* {equi} {fold x v} (unfold a ty) with normalizeDeriv ty | normalizeDeriv-Value ty | normalizeDeriv-eval* ty
normalizeDeriv-eval* {equi} {fold x v} (unfold a ty) | fold a ty₁ | fold tyV′ | evals = trans⟶d* (unfold-d* evals) (underlying⟶d* (unfoldFold tyV′))


-- stepResult : Result 0 0 → Term 0 0
-- stepResult (continue t) = t
-- stepResult (done v) = ⌜ v ⌝

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

⊢⌜⌝-ValueDeriv : ∀ {s v τ} → (ty : [ s ] [] ⊢val v ∈ τ) → ValueDeriv (⊢⌜ ty ⌝)
⊢⌜⌝-ValueDeriv (Λ ty) = Λ ty
⊢⌜⌝-ValueDeriv (λ' a ty) = λ' ty
⊢⌜⌝-ValueDeriv {s = iso} (fold a ty) = fold (⊢⌜⌝-ValueDeriv ty)
⊢⌜⌝-ValueDeriv {s = equi} (fold a ty) = fold (⊢⌜⌝-ValueDeriv ty)


derivFollows : ∀ {τ t₁ t₂} (ty : [ equi ] [] ⊢ t₁ ∈ τ) →
               (eval : t₁ ⟶t t₂) →
               ty ⟶d* preservation ty eval
derivFollows (ty [ b ]) (App eval) = App-d* (derivFollows ty eval)
derivFollows (ty [ b ]) Beta with normalizeDeriv ty | normalizeDeriv-Value ty | normalizeDeriv-eval* ty
derivFollows (ty [ b ]) Beta | .(Λ ty′) | Λ ty′ | evals =
  trans⟶d* (App-d* evals) (underlying⟶d* Beta)
derivFollows (ty₁ · ty₂) (app₁ eval) = app₁-d* (derivFollows ty₁ eval)
derivFollows (ty₁ · ty₂) (app₂ eval) with normalizeDeriv ty₁ | normalizeDeriv-Value ty₁ | normalizeDeriv-eval* ty₁
derivFollows (ty₁ · ty₂) (app₂ eval) | ty₁′ | vty₁′ | evals =
  trans⟶d* (app₁-d* evals) (app₂-d* vty₁′ (derivFollows ty₂ eval))
derivFollows (ty₁ · ty₂) beta
  with normalizeDeriv ty₁ | normalizeDeriv-Value ty₁ | normalizeDeriv-eval* ty₁
     | normalizeDeriv ty₂ | normalizeDeriv-Value ty₂ | normalizeDeriv-eval* ty₂
derivFollows (ty₁ · ty₂) beta
  | .(λ' _ ty₁′) | λ' ty₁′ | evals₁ | ty₂′ | vty₂′ | evals₂ =
  trans⟶d* (app₁-d* evals₁)
    (trans⟶d* (app₂-d* (λ' ty₁′) evals₂)
    (underlying⟶d* (beta ty₁′ ty₂′ vty₂′)))
derivFollows (fold a ty) eval = fold-d* (derivFollows ty eval)
derivFollows (unfold a ty) eval = unfold-d* (derivFollows ty eval)

derivFollows* : ∀ {τ t₁ t₂} (ty : [ equi ] [] ⊢ t₁ ∈ τ) →
               (evals : t₁ ⟶t* t₂) →
               ty ⟶d* preservation* ty evals
derivFollows* ty refl⟶t* = refl⟶d*
derivFollows* ty (underlying⟶t* eval) = derivFollows ty eval
derivFollows* ty (trans⟶t* evals₁ evals₂) =
  trans⟶d* (derivFollows* ty evals₁) (derivFollows* (preservation* ty evals₁) evals₂)

