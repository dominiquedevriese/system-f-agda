module SystemF.DerivationSemantics where

open import Data.Nat using (suc; zero)
open import Data.Vec using (_∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.All as MaybeAll
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import SystemF.WtTerm
open import SystemF.Term
open import SystemF.Type
open import SystemF.Reduction

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
           fold a ty ⟶d fold a ty′
  unfold : ∀ {t t′ a} {ty : [ s ] [] ⊢ t ∈ μ a} {ty′ : [ s ] [] ⊢ t′ ∈ μ a} →
           unfold a ty ⟶d unfold a ty′

data _⟶d*_ {s} {τ} {t₁} (ty₁ : [ s ] [] ⊢ t₁ ∈ τ) : ∀ {t₂} (ty₂ : [ s ] [] ⊢ t₂ ∈ τ) → Set where
  refl⟶d* : ty₁ ⟶d* ty₁
  underlying⟶d* : ∀ {t₂} {ty₂ : [ s ] [] ⊢ t₂ ∈ τ} → ty₁ ⟶d ty₂ → ty₁ ⟶d* ty₂
  trans⟶d* : ∀ {t₂ t₃} {ty₂ : [ s ] [] ⊢ t₂ ∈ τ} {ty₃ : [ s ] [] ⊢ t₃ ∈ τ} → ty₁ ⟶d* ty₂ → ty₂ ⟶d* ty₃ → ty₁ ⟶d* ty₃

fold-d* : ∀ {s t t′ a} {ty : [ s ] [] ⊢ t ∈ a [/tp μ a ]} {ty′ : [ s ] [] ⊢ t′ ∈ a [/tp μ a ]} →
          ty ⟶d* ty′ → fold a ty ⟶d* fold a ty′
fold-d* refl⟶d* = refl⟶d*
fold-d* (underlying⟶d* eval) = underlying⟶d* fold
fold-d* (trans⟶d* eval₁ eval₂) = trans⟶d* (fold-d* eval₁) (fold-d* eval₂)

unfold-d* : ∀ {s t t′ a} {ty : [ s ] [] ⊢ t ∈ μ a} {ty′ : [ s ] [] ⊢ t′ ∈ μ a} →
          ty ⟶d* ty′ → unfold a ty ⟶d* unfold a ty′
unfold-d* refl⟶d* = refl⟶d*
unfold-d* (underlying⟶d* eval) = underlying⟶d* unfold
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


stepResult : Result 0 0 → Term 0 0
stepResult (continue t) = t
stepResult (done v) = ⌜ v ⌝

preservation : ∀ {s τ t} (ty : [ s ] [] ⊢ t ∈ τ) →
               MaybeAll.All (λ res → [ s ] [] ⊢ stepResult res ∈ τ) (step t)
preservation {t = t} ty with step t | ⊢step ty
preservation {t = t} ty | just .(continue _) | just (⊢continue ty′) = just ty′
preservation {t = t} ty | just .(done _) | just (⊢done ty′) = just ⊢⌜ ty′ ⌝
preservation {t = t} ty | Data.Maybe.nothing | ty′ = MaybeAll.nothing

preservation* : ∀ k {s τ t} (ty : [ s ] [] ⊢ t ∈ τ) →
                MaybeAll.All (λ res → [ s ] [] ⊢ stepResult res ∈ τ) (step* k t)
preservation* zero {t = t} ty = just ty
preservation* (suc k) {t = t} ty with step t | preservation ty
preservation* (suc k) {t = t} ty | nothing | nothing = nothing
preservation* (suc k) {t = t} ty | just (continue t′) | just ty′ = preservation* k ty′
preservation* (suc k) {t = t} ty | just (done v) | just ty′ = just ty′

⊢⌜⌝-ValueDeriv : ∀ {s v τ} → (ty : [ s ] [] ⊢val v ∈ τ) → ValueDeriv (⊢⌜ ty ⌝)
⊢⌜⌝-ValueDeriv (Λ ty) = Λ ty
⊢⌜⌝-ValueDeriv (λ' a ty) = λ' ty
⊢⌜⌝-ValueDeriv {s = iso} (fold a ty) = fold (⊢⌜⌝-ValueDeriv ty)
⊢⌜⌝-ValueDeriv {s = equi} (fold a ty) = fold (⊢⌜⌝-ValueDeriv ty)

derivFollows : ∀ {τ t} (ty : [ equi ] [] ⊢ t ∈ τ) →
               MaybeAllAll (λ ty′ → ty ⟶d* ty′) (preservation ty)
derivFollows {t = t} (fold a ty) with step t | ⊢step ty | derivFollows ty
derivFollows {t = t} (fold a ty) | .(just (continue _)) | just (⊢continue ty′) | just evals =
  just (fold-d* evals)
derivFollows {t = t} (fold a ty) | .(just (done _)) | just (⊢done ty′) | just evals =
  just (fold-d* evals)
derivFollows {t = t} (fold a ty) | .nothing | nothing | _ = nothing
derivFollows {t = t} (unfold a ty) with step t | ⊢step ty | derivFollows ty
derivFollows {t = t} (unfold a ty) | .(just (continue _)) | just (⊢continue ty′) | just evals =
  just (unfold-d* evals)
derivFollows {t = t} (unfold a ty) | .(just (done _)) | just (⊢done (fold .a ty′)) | just evals =
  just (trans⟶d* (unfold-d* evals)
    (underlying⟶d* (unfoldFold (⊢⌜⌝-ValueDeriv ty′))))
derivFollows {t = t} (unfold a ty) | .nothing | nothing | _ = nothing
derivFollows {t = Λ t} (Λ ty) = just refl⟶d*
derivFollows {t = λ' x t} (λ' .x ty) = just refl⟶d*
-- derivFollows {t = μ x t} (μ .x ty) = {!!}
derivFollows {t = t [ x ]} (ty [ .x ]) with step t | ⊢step ty | derivFollows ty
derivFollows {_} {t [ x ]} (ty [ .x ]) | .(just (continue _)) | just (⊢continue ty′) | just evals =
  just (App-d* evals)
derivFollows {_} {t [ x ]} (ty [ .x ]) | .(just (done (Λ _))) | just (⊢done (Λ x₁)) | just evals =
  just (trans⟶d* (App-d* evals) (underlying⟶d* Beta))
derivFollows {_} {t [ x ]} (ty [ .x ]) | .nothing | nothing | _ = nothing
derivFollows {t = t₁ · t₂} (ty₁ · ty₂) with step t₁ | ⊢step ty₁ | derivFollows ty₁
derivFollows {_} {t₁ · t₂} (ty₁ · ty₂) | .nothing | nothing | _ = nothing
derivFollows {_} {t₁ · t₂} (ty₁ · ty₂) | .(just (continue _)) | just (⊢continue ty₁′) | just evals₁ =
  just (app₁-d* evals₁)
derivFollows {_} {t₁ · t₂} (ty₁ · ty₂) | .(just (done (λ' a _))) | just (⊢done (λ' a ty₁′)) | just evals₁ with step t₂ | ⊢step ty₂ | derivFollows ty₂
derivFollows {_} {t₁ · t₂} (ty₁ · ty₂) | .(just (done (λ' a _))) | just (⊢done (λ' a ty₁′)) | just evals₁ | .nothing | nothing | _ = nothing
derivFollows {_} {t₁ · t₂} (ty₁ · ty₂) | .(just (done (λ' a _))) | just (⊢done (λ' a ty₁′)) | just evals₁ | .(just (continue _)) | just (⊢continue ty₂′) | just evals₂ =
  just (trans⟶d* (app₁-d* evals₁)
    (app₂-d* (λ' ty₁′) evals₂))
derivFollows {_} {t₁ · t₂} (ty₁ · ty₂) | .(just (done (λ' a _))) | just (⊢done (λ' a ty₁′)) | just evals₁ | .(just (done _)) | just (⊢done ty₂′) | just evals₂ =
  just (trans⟶d* (app₁-d* evals₁)
    (trans⟶d* (app₂-d* (λ' ty₁′) evals₂)
    (underlying⟶d* (beta ty₁′ ⊢⌜ ty₂′ ⌝ (⊢⌜⌝-ValueDeriv ty₂′)))))


derivFollows* : ∀ k {τ t} (ty : [ equi ] [] ⊢ t ∈ τ) →
                MaybeAllAll (λ ty′ → ty ⟶d* ty′) (preservation* k ty)
derivFollows* zero ty = just refl⟶d*
derivFollows* (suc k) {t = t} ty with step t | preservation ty | derivFollows ty
derivFollows* (suc k) {t = t} ty | nothing | nothing | _ = nothing
derivFollows* (suc k) {t = t} ty | just (continue t′) | just ty′ | just evals with step* k t′ | preservation* k ty′ | derivFollows* k ty′
derivFollows* (suc k) {t = t} ty | just (continue t′) | just ty′ | just evals | .nothing | nothing | _ = nothing
derivFollows* (suc k) {t = t} ty | just (continue t′) | just ty′ | just evals | .(just _) | just x | just evals′ = just (trans⟶d* evals evals′)
derivFollows* (suc k) {t = t} ty | just (done v) | just ty′ | just evals = just evals
