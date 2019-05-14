module SystemF.IsoEquiLink where

open import Data.Fin using (Fin; zero; suc; inject+)
open import Data.Fin.Substitution using (Sub; Lift; module VarSubst)
open import Data.Fin.Substitution.Lemmas using ()
open import Data.Nat using (ℕ; suc; zero)
open import Data.Vec using (Vec; []; _∷_; map; lookup)
open import Data.Vec.Properties using (lookup-map; map-∘; map-cong)
open import Data.Sum using (_⊎_)
open import Data.Product using (∃; _,_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.All as MaybeAll using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; cong₂; subst₂; sym; trans; module ≡-Reasoning)
open import Function using (_∘_)

open import SystemF.WtTerm
open import SystemF.Term
open import SystemF.Type
open import SystemF.Contexts
open import SystemF.ReductionJudgement
open import SystemF.DerivationSemantics

open TypeSubst       using () renaming (_[/_]  to _[/tp_]; _/_ to _/tp_)
open TermTypeSubst   using () renaming (_[/_]  to _[/tmTp_]; _/_ to _/tmTp_; weaken to weakenTmTp)
open TermTermSubst   using (TermSub) renaming (_[/_]  to _[/tmTm_]; _/_ to _/tm_; weaken to weakenTmTm; _/Var_ to _/Var-tm_)
open WtTermTypeSubst using () renaming (_[/_]′ to _[/⊢tmTp_]; _/_ to _/⊢tmTp_; weaken to weaken-⊢tmTp; weakenAll to weakenAll-⊢tmTp)
open WtTermTermSubst using () renaming (_[/_]  to _[/⊢tmTm_]; weakenAll to weakenAll-⊢tmTm; weaken to weaken-⊢tmTm; _/Var_ to _/⊢Var_)

open CtxSubst  using () renaming (weaken to weakenCtx)
open CtxLemmas using () renaming (_/Var_ to _/CtxVar_)


erase : ∀ {m n} → Term m n → Term m n
erase (var x) = var x
erase (Λ t) = Λ (erase t)
erase (λ' x t) = λ' x (erase t)
-- erase (μ x t) = μ x (erase t)
erase (t [ x ]) = erase t [ x ]
erase (t₁ · t₂) = erase t₁ · erase t₂
erase (fold x t) = erase t
erase (unfold x t) = erase t

erase-ty : ∀ {m n} {t : Term m n} {Γ : Ctx m n} {τ : Type n}→
           [ iso ] Γ ⊢ t ∈ τ →
           [ equi ] Γ ⊢ erase t ∈ τ
erase-ty (var x) = var x
erase-ty (Λ ty) = Λ (erase-ty ty)
erase-ty (λ' a ty) = λ' a (erase-ty ty)
-- erase-ty (μ a ty) = μ a (erase-ty ty)
erase-ty (ty [ b ]) = erase-ty ty [ b ]
erase-ty (ty₁ · ty₂) = erase-ty ty₁ · erase-ty ty₂
erase-ty (fold a ty) = fold a (erase-ty ty)
erase-ty (unfold a ty) = unfold a (erase-ty ty)


erase-val : ∀ {m n} (v : Val m n) → Val m n
erase-val (Λ t) = Λ (erase t)
erase-val (λ' a t) = λ' a (erase t)
erase-val (fold a v) = erase-val v

erase-⌜⌝ : (v : Val 0 0) → erase (⌜ v ⌝) ≡ ⌜ erase-val v ⌝
erase-⌜⌝ (Λ x) = refl
erase-⌜⌝ (λ' x x₁) = refl
erase-⌜⌝ (fold x v) = erase-⌜⌝ v

module TermTypeAppErase {T : ℕ → Set} (l : Lift T Type) where
  open Lift l hiding (var)
  open TypeSubst.TypeApp l renaming (_/_ to _/tpl_)
  open TermTypeSubst.TermTypeApp l using (_/_)

  erase-sub : ∀ {m n k} (t : Term m n) (σ : Sub T n k) → erase t / σ ≡ erase (t / σ)
  erase-sub (var x) σ = refl
  erase-sub (Λ t) σ = cong Λ (erase-sub t (σ ↑))
  erase-sub (λ' a t) σ = cong (λ' (a /tpl σ)) (erase-sub t σ)
  erase-sub (t [ τ ]) σ = cong (_[ τ /tpl σ ]) (erase-sub t σ)
  erase-sub (t₁ · t₂) σ = cong₂ _·_ (erase-sub t₁ σ) (erase-sub t₂ σ)
  erase-sub (fold τ t) σ = erase-sub t σ
  erase-sub (unfold τ t) σ = erase-sub t σ

erase-[/tmTp] : ∀ (t : Term 0 1) {a} → erase t [/tmTp a ] ≡ erase (t [/tmTp a ])
erase-[/tmTp] t {τ} = erase-sub t (sub τ)
  where open TypeSubst using (termLift; sub)
        open TermTypeAppErase termLift

erase-weakenType : ∀ {m n} (t : Term m n) → TermTypeLemmas.weaken (erase t) ≡ erase (TermTypeLemmas.weaken t)
erase-weakenType t = erase-sub t VarSubst.wk
  where open TypeSubst using (varLift)
        open TermTypeAppErase varLift

open TermTermSubst using (TermLift; TermSub; termLift)

module TermTermAppErase where
  open TermLift termLift
  open TermTermSubst using (Fin′; module TermTermApp; varLift; weaken)
  open TermLift varLift using () renaming (_↑tp to _↑tpvar; _↑tm to _↑tmvar)
  open TermTermApp varLift using () renaming (_/_ to _/var_)
  open TermTermApp termLift using (_/_)

  erase-sub-var : ∀ {m n k} (t : Term m n) (σ : TermSub Fin′ m n k) → erase t /var σ ≡ erase (t /var σ)
  erase-sub-var (var x) σ = refl
  erase-sub-var {n = n} (Λ t) σ = cong Λ (erase-sub-var t (_↑tpvar {n = n} σ))
  erase-sub-var {n = n} (λ' a t) σ = cong (λ' a) (erase-sub-var t (_↑tmvar {n = n} σ))
  erase-sub-var (t [ τ ]) σ = cong (_[ τ ]) (erase-sub-var t σ)
  erase-sub-var (t₁ · t₂) σ = cong₂ _·_ (erase-sub-var t₁ σ) (erase-sub-var t₂ σ)
  erase-sub-var (fold τ t) σ = erase-sub-var t σ
  erase-sub-var (unfold τ t) σ = erase-sub-var t σ

  erase-weaken : ∀ {m n} (t : Term m n) → weaken (erase t) ≡ erase (weaken t)
  erase-weaken t = erase-sub-var t VarSubst.wk

  erase-sub : ∀ {m n k} (t : Term m n) (σ : TermSub Term m n k) → erase t / map erase σ ≡ erase (t / σ)
  erase-sub (var x) σ = lookup-map x erase σ
  erase-sub (Λ t) σ = cong Λ (trans (cong (erase t /_) h) (erase-sub t (σ ↑tp)))
    where
      open ≡-Reasoning
      h : map TermTypeLemmas.weaken (map erase σ) ≡
          map erase (map TermTypeLemmas.weaken σ)
      h = begin
            map TermTypeLemmas.weaken (map erase σ)
              ≡⟨ sym (map-∘ TermTypeLemmas.weaken erase σ) ⟩
            map (TermTypeLemmas.weaken ∘ erase) σ
              ≡⟨ map-cong (λ t → erase-weakenType t) σ ⟩
            map (erase ∘ TermTypeLemmas.weaken) σ
              ≡⟨ map-∘ erase TermTypeLemmas.weaken σ ⟩
            map erase (map TermTypeLemmas.weaken σ) ∎
  erase-sub (λ' a t) σ = cong (λ' a) (trans (cong (erase t /_) h) (erase-sub t (σ ↑tm)))
    where
      open ≡-Reasoning
      open TermTermSubst using (_↑; weaken)
      h : map erase σ ↑ ≡ map erase (σ ↑)
      h = cong (_∷_ (var zero))
          (begin
            map weaken (map erase σ) ≡⟨ sym (map-∘ weaken erase σ) ⟩
            map (weaken ∘ erase) σ ≡⟨ map-cong (λ t → erase-weaken t) σ ⟩
            map (erase ∘ weaken) σ ≡⟨ map-∘ erase weaken σ ⟩
            map erase (map weaken σ)
          ∎)
  erase-sub (t [ τ ]) σ = cong (_[ τ ]) (erase-sub t σ)
  erase-sub (t₁ · t₂) σ = cong₂ _·_ (erase-sub t₁ σ) (erase-sub t₂ σ)
  erase-sub (fold τ t) σ = erase-sub t σ
  erase-sub (unfold τ t) σ = erase-sub t σ

erase-[/tmTm] : ∀ (t₁ : Term 1 0) {t₂} → erase t₁ [/tmTm erase t₂ ] ≡ erase (t₁ [/tmTm t₂ ])
erase-[/tmTm] t {t₂} = erase-sub t (sub t₂) -- erase-sub t (sub t₂)
  where open TermTermSubst using (sub)
        open TermTermAppErase

erase-[/tmVal] : ∀ (t₁ : Term 1 0) (v₂ : Val 0 0) →
                 erase t₁ [/tmTm ⌜ erase-val v₂ ⌝ ] ≡ erase (t₁ [/tmTm ⌜ v₂ ⌝ ])
erase-[/tmVal] t₁ v₂ =
  begin
    erase t₁ [/tmTm ⌜ erase-val v₂ ⌝ ]
      ≡⟨ cong (erase t₁ [/tmTm_]) (sym (erase-⌜⌝ v₂)) ⟩
    erase t₁ [/tmTm erase ⌜ v₂ ⌝ ]
      ≡⟨ erase-[/tmTm] t₁ ⟩
    erase (t₁ [/tmTm ⌜ v₂ ⌝ ])
  ∎
  where open ≡-Reasoning

erase-eval : ∀ {t₁ t₂} → t₁ ⟶t t₂ → erase t₁ ⟶t* erase t₂
erase-eval (App eval) = App⟶t* (erase-eval eval)
erase-eval {t₁ = (Λ t₁) [ a ]} Beta = subst ((Λ (erase t₁) [ a ]) ⟶t*_) (erase-[/tmTp] t₁) (underlying⟶t* Beta)
erase-eval (app₁ eval) = app₁⟶t* (erase-eval eval)
erase-eval (app₂ {v₁ = v₁} eval) rewrite erase-⌜⌝ v₁ = app₂⟶t* (erase-eval eval)
erase-eval {t₁ = (λ' a t₁) · _} (beta {v₂ = v₂}) rewrite erase-⌜⌝ v₂ =
  subst ((λ' a (erase t₁) · _) ⟶t*_) (erase-[/tmVal] t₁ v₂) (underlying⟶t* beta)
erase-eval (fold eval) = erase-eval eval
erase-eval (unfold eval) = erase-eval eval
erase-eval unfoldFold = refl⟶t*

erase-evals : ∀ {t₁ t₂} → t₁ ⟶t* t₂ → erase t₁ ⟶t* erase t₂
erase-evals refl⟶t* = refl⟶t*
erase-evals (underlying⟶t* x) = erase-eval x
erase-evals (trans⟶t* evals₁ evals₂) = trans⟶t* (erase-evals evals₁) (erase-evals evals₂)

erase-⇓ : {t : Term 0 0} → t ⇓ → erase t ⇓
erase-⇓ {t} (term v evals) = term (erase-val v) (subst (erase t ⟶t*_) (erase-⌜⌝ v) (erase-evals evals))

erase-context : ∀ {mᵢ nᵢ mₒ nₒ} → Context mᵢ nᵢ mₒ nₒ → Context mᵢ nᵢ mₒ nₒ
erase-context hole = hole
erase-context (Λ ctx) = Λ (erase-context ctx)
erase-context (λ' a ctx) = λ' a (erase-context ctx)
erase-context (ctx [ a ]) = erase-context ctx [ a ]
erase-context (ctx ·₁ t₂) = erase-context ctx ·₁ erase t₂
erase-context (t₁ ·₂ ctx) = erase t₁ ·₂ erase-context ctx
erase-context (fold a ctx) = erase-context ctx
erase-context (unfold a ctx) = erase-context ctx

erase-plug : ∀ {mᵢ nᵢ mₒ nₒ} (ctx : Context mᵢ nᵢ mₒ nₒ) {t} →
             erase (plug ctx t) ≡ plug (erase-context ctx) (erase t)
erase-plug hole = refl
erase-plug (Λ ctx) = cong Λ (erase-plug ctx)
erase-plug (λ' a ctx) = cong (λ' a) (erase-plug ctx)
erase-plug (ctx [ a ]) = cong (_[ a ]) (erase-plug ctx)
erase-plug (ctx ·₁ t₂) = cong (_· erase t₂) (erase-plug ctx)
erase-plug (t₁ ·₂ ctx) = cong (erase t₁ ·_) (erase-plug ctx)
erase-plug (fold a ctx) = erase-plug ctx
erase-plug (unfold a ctx) = erase-plug ctx

erase-context-ty : ∀ {mᵢ nᵢ mₒ nₒ} {C : Context mᵢ nᵢ mₒ nₒ}
                   {Γᵢ : Ctx mᵢ nᵢ} {τᵢ : Type nᵢ} {Γₒ : Ctx mₒ nₒ} {τₒ : Type nₒ} →
                   [ iso ]⊢ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ τₒ →
                   [ equi ]⊢ (erase-context C) ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ τₒ
erase-context-ty hole = hole
erase-context-ty (Λ tyC) = Λ (erase-context-ty tyC)
erase-context-ty (λ' a tyC) = λ' a (erase-context-ty tyC)
erase-context-ty (tyC [ τₒ ]) = erase-context-ty tyC [ τₒ ]
erase-context-ty (tyC ·₁ ty) = erase-context-ty tyC ·₁ erase-ty ty
erase-context-ty (ty ·₂ tyC) = erase-ty ty ·₂ erase-context-ty tyC
erase-context-ty (fold a tyC) = fold a (erase-context-ty tyC)
erase-context-ty (unfold a tyC) = unfold a (erase-context-ty tyC)


unerase : ∀ {m n} {t : Term m n} {Γ : Ctx m n} {τ : Type n}→
           [ equi ] Γ ⊢ t ∈ τ →
           Term m n
unerase (var x) = var x
unerase (Λ ty) = Λ (unerase ty)
unerase (λ' a ty) = λ' a (unerase ty)
-- unerase (μ a ty) = μ a (unerase ty)
unerase (ty [ b ]) = unerase ty [ b ]
unerase (ty₁ · ty₂) = unerase ty₁ · unerase ty₂
unerase (fold a ty) = fold a (unerase ty)
unerase (unfold a ty) = unfold a (unerase ty)

unerase-ty : ∀ {m n} {t : Term m n} {Γ : Ctx m n} {τ : Type n}→
           (ty : [ equi ] Γ ⊢ t ∈ τ) →
           [ iso ] Γ ⊢ unerase ty ∈ τ
unerase-ty (var x) = var x
unerase-ty (Λ ty) = Λ (unerase-ty ty)
unerase-ty (λ' a ty) = λ' a (unerase-ty ty)
-- unerase-ty (μ a ty) = μ a (unerase-ty ty)
unerase-ty (ty [ b ]) = unerase-ty ty [ b ]
unerase-ty (ty₁ · ty₂) = unerase-ty ty₁ · unerase-ty ty₂
unerase-ty (fold a ty) = fold a (unerase-ty ty)
unerase-ty (unfold a ty) = unfold a (unerase-ty ty)

unerase-erase : ∀ {m n} {t : Term m n} {Γ : Ctx m n} {τ : Type n}→
                (ty : [ iso ] Γ ⊢ t ∈ τ) →
                unerase (erase-ty ty) ≡ t
unerase-erase (var x) = refl
unerase-erase (Λ ty) = cong Λ (unerase-erase ty)
unerase-erase (λ' a ty) = cong (λ' a) (unerase-erase ty)
-- unerase-erase (μ a ty) = cong (μ a) (unerase-erase ty)
unerase-erase (ty [ b ]) = cong (λ t → t [ b ]) (unerase-erase ty)
unerase-erase (ty₁ · ty₂) = cong₂ _·_ (unerase-erase ty₁) (unerase-erase ty₂)
unerase-erase (fold a ty) = cong (fold a) (unerase-erase ty)
unerase-erase (unfold a ty) = cong (unfold a) (unerase-erase ty)

erase-unerase : ∀ {m n} {t : Term m n} {Γ : Ctx m n} {τ : Type n}→
                (ty : [ equi ] Γ ⊢ t ∈ τ) →
                erase (unerase ty) ≡ t
erase-unerase (var x) = refl
erase-unerase (Λ ty) = cong Λ (erase-unerase ty)
erase-unerase (λ' a ty) = cong (λ' a) (erase-unerase ty)
-- erase-unerase (μ a ty) = cong (μ a) (erase-unerase ty)
erase-unerase (ty [ b ]) = cong (λ t → t [ b ]) (erase-unerase ty)
erase-unerase (ty₁ · ty₂) = cong₂ _·_ (erase-unerase ty₁) (erase-unerase ty₂)
erase-unerase (fold a ty) = erase-unerase ty
erase-unerase (unfold a ty) = erase-unerase ty

unerase-vderiv : {t : Term 0 0} {Γ : Ctx 0 0} {τ : Type 0}→
                 {ty : [ equi ] Γ ⊢ t ∈ τ} → (vty : ValueDeriv ty) →
                 Val 0 0
unerase-vderiv (λ' {a = a} ty) = λ' a (unerase ty)
unerase-vderiv (Λ ty) = Λ (unerase ty)
unerase-vderiv (fold {a = a} vty) = fold a (unerase-vderiv vty)

unerase-vty : {t : Term 0 0} {τ : Type 0}→
              {ty : [ equi ] [] ⊢ t ∈ τ} → (vty : ValueDeriv ty) →
              unerase ty ≡ ⌜ unerase-vderiv vty ⌝
unerase-vty (λ' ty) = refl
unerase-vty (Λ ty) = refl
unerase-vty (fold vty) = cong (fold _) (unerase-vty vty)

unerase-⊢substCtx : ∀ {m n} {Γ₁ Γ₂ : Ctx m n} {t : Term m n} {a : Type n} →
                    (eqΓ : Γ₁ ≡ Γ₂) → (ty : [ equi ] Γ₁ ⊢ t ∈ a) →
                    unerase (⊢substCtx eqΓ ty) ≡ unerase ty
unerase-⊢substCtx refl ty = refl

unerase-⊢substTp : ∀ {m n} {Γ : Ctx m n} {t : Term m n} {a₁ a₂ : Type n} →
                   (eq : a₁ ≡ a₂) → (ty : [ equi ] Γ ⊢ t ∈ a₁) →
                   unerase (⊢substTp eq ty) ≡ unerase ty
unerase-⊢substTp refl ty = refl

unerase-tysub : ∀ {m n k} {t₁ : Term m n} {τ₁} {Γ : Ctx m n}
                (σ : Sub Type n k) →
                (ty₁ : [ equi ] Γ ⊢ t₁ ∈ τ₁) →
                unerase (ty₁ /⊢tmTp σ ) ≡ unerase ty₁ /tmTp σ
unerase-tysub σ (var x) = unerase-⊢substTp (TypeLemmas.lookup-⊙ x) (var x)
unerase-tysub {Γ = Γ} σ (Λ ty₁) =
  cong Λ
    (trans (unerase-⊢substCtx (sym (TypeLemmas.map-weaken-⊙ Γ σ)) (ty₁ /⊢tmTp σ TypeLemmas.↑))
      (unerase-tysub (σ TypeLemmas.↑) ty₁))
unerase-tysub σ (λ' a ty₁) = cong (λ' (a /tp σ)) (unerase-tysub σ ty₁)
unerase-tysub σ (_[_] {a = a} ty₁ b) = trans (unerase-⊢substTp (sym (TypeLemmas.sub-commutes a)) ((ty₁ /⊢tmTp σ) [ b TypeLemmas./ σ ]))
                              (cong (_[ b TypeLemmas./ σ ]) (unerase-tysub σ ty₁))
unerase-tysub σ (ty₁ · ty₂) = cong₂ _·_ (unerase-tysub σ ty₁) (unerase-tysub σ ty₂)
unerase-tysub σ (fold a ty₁) = cong (fold (a TypeLemmas./ σ TypeLemmas.↑))
                               (trans (unerase-⊢substTp (TypeLemmas.sub-commutes a) (ty₁ /⊢tmTp σ))
                               (unerase-tysub σ ty₁))
unerase-tysub σ (unfold a ty₁) =
  trans (unerase-⊢substTp (sym (TypeLemmas.sub-commutes a)) (unfold (a TypeLemmas./ σ TypeLemmas.↑) (ty₁ /⊢tmTp σ)))
    (cong (unfold (a TypeLemmas./ σ TypeLemmas.↑)) (unerase-tysub σ ty₁))

unerase-[/⊢tmTp] : ∀ {t₁ : Term 0 1} {τ₁}
                   (ty₁ : [ equi ] weakenCtx [] ⊢ t₁ ∈ τ₁) τ₂ →
                   unerase (ty₁ [/⊢tmTp τ₂ ]) ≡ unerase ty₁ [/tmTp τ₂ ]
unerase-[/⊢tmTp] ty₁ τ₂ = unerase-tysub (sub τ₂) ty₁
  where open TypeSubst using (sub)


open WtTermTermSubst using ([_]_⇒_⊢_) renaming (_/_ to _/⊢tm_; _↑ to _↑⊢tm; sub to sub-⊢tmTm)

unerase-tmsub : ∀ {m n k : ℕ} {Γ : Ctx m n} {Δ : Ctx k n} {ρ : TermSub Term m n k} →
                [ equi ] Γ ⇒ Δ ⊢ ρ → TermSub Term m n k
unerase-tmsub [] = []
unerase-tmsub (ty ∷ tyρ) = unerase ty ∷ unerase-tmsub tyρ

unerase-lookup-⊢ : ∀ {m n k} {Γ : Ctx m n} {ts : Vec (Term m n) k} {as : Vec (Type n) k} →
                   (x : Fin k) → (tyρ : [ equi ] Γ ⊢ⁿ ts ∈ as) →
                   unerase (lookup-⊢ x tyρ) ≡ lookup (unerase-tmsub tyρ) x
unerase-lookup-⊢ zero (ty ∷ tyρ) = refl
unerase-lookup-⊢ (suc x) (ty ∷ tyρ) = unerase-lookup-⊢ x tyρ

unerase-⊢subst : ∀ {m n} {Γ₁ Γ₂ : Ctx m n} {t₁ t₂ : Term m n} {a₁ a₂ : Type n} →
                 (eqΓ : Γ₁ ≡ Γ₂) → (eqt : t₁ ≡ t₂) → (eqτ : a₁ ≡ a₂) →
                 (ty : [ equi ] Γ₁ ⊢ t₁ ∈ a₁) →
                 unerase (⊢subst eqΓ eqt eqτ ty) ≡ unerase ty
unerase-⊢subst refl refl refl hyp = refl

unerase-weaken-⊢tmTp : ∀ {n} {k} {t : Term k n} {a : Type n}
                         {Δ : Ctx k n} (ty : [ equi ] Δ ⊢ t ∈ a) →
                       unerase (weaken-⊢tmTp ty) ≡ weakenTmTp (unerase ty)
unerase-weaken-⊢tmTp {t = t} {a = a} ty =
  trans (unerase-⊢subst (sym map-weaken) (/-wkTmTp t) (/-wk {t = a}) (ty /⊢tmTp wk))
    (trans (unerase-tysub wk ty)
      (/-wkTmTp (unerase ty)))
  where open TypeLemmas using (map-weaken; /-wk; wk)
        open TermTypeLemmas renaming (/-wk to /-wkTmTp)

unerase-tmsub-weakenAll-⊢tmTp :
  ∀ {n} {m} {k} {Γ : Ctx m n} {Δ : Ctx k n}
    {ρ : Vec (Term k n) m} (tyρ : [ equi ] Δ ⊢ⁿ ρ ∈ Γ) →
    unerase-tmsub (weakenAll-⊢tmTp tyρ) ≡ map weakenTmTp (unerase-tmsub tyρ)
unerase-tmsub-weakenAll-⊢tmTp [] = refl
unerase-tmsub-weakenAll-⊢tmTp (ty ∷ tyρ) = cong₂ _∷_ (unerase-weaken-⊢tmTp ty) (unerase-tmsub-weakenAll-⊢tmTp tyρ)

unerase-/⊢Var : ∀ {m n k} {Γ : Ctx k n} {t : Term m n} {a : Type n}
               (ρ : Sub Fin m k) → (ty : [ equi ] ρ /CtxVar Γ ⊢ t ∈ a) →
               unerase {Γ = Γ} (ρ /⊢Var ty) ≡ unerase ty /Var-tm ρ
unerase-/⊢Var {Γ = Γ} ρ (var x) =
  unerase-⊢substTp (sym (CtxLemmas./Var-lookup x ρ Γ)) (var (lookup ρ x)) 
unerase-/⊢Var {Γ = Γ} ρ (Λ ty) =
  cong Λ (
    trans (unerase-/⊢Var ρ (⊢substCtx (CtxLemmas./Var-weaken ρ Γ) ty))
      (cong (_/Var-tm ρ) (unerase-⊢substCtx (CtxLemmas./Var-weaken ρ Γ) ty)))
unerase-/⊢Var {Γ = Γ} ρ (λ' a ty) =
  cong (λ' a) (
    trans (unerase-/⊢Var (ρ VarSubst.↑) (⊢substCtx (CtxLemmas./Var-∷ a ρ Γ) ty))
      (cong (_/Var-tm (ρ VarSubst.↑)) (unerase-⊢substCtx (CtxLemmas./Var-∷ a ρ Γ) ty)))
unerase-/⊢Var ρ (ty [ b ]) =
  cong (_[ b ]) (unerase-/⊢Var ρ ty)
unerase-/⊢Var ρ (ty₁ · ty₂) = cong₂ _·_ (unerase-/⊢Var ρ ty₁) (unerase-/⊢Var ρ ty₂)
unerase-/⊢Var ρ (fold a ty) = cong (fold a) (unerase-/⊢Var ρ ty)
unerase-/⊢Var ρ (unfold a ty) = cong (unfold a) (unerase-/⊢Var ρ ty)

unerase-weaken-⊢tmTm : ∀ {n} {k} {t : Term k n} {a : Type n} {b : Type n}
                         {Δ : Ctx k n} (ty : [ equi ] Δ ⊢ t ∈ a) →
                       unerase (weaken-⊢tmTm {b = b} ty) ≡ weakenTmTm (unerase ty)
unerase-weaken-⊢tmTm {b = b} {Δ = Δ} ty =
  trans (unerase-/⊢Var VarSubst.wk (⊢substCtx (CtxLemmas.wkVar-/Var-∷ Δ b) ty))
    (cong (_/Var-tm VarSubst.wk) (unerase-⊢substCtx (CtxLemmas.wkVar-/Var-∷ Δ b) ty))

unerase-tmsub-weakenAll-⊢tmTm :
  ∀ {n} {m} {k} {Γ : Ctx m n} {Δ : Ctx k n} {b : Type n}
    {ρ : Vec (Term k n) m} (tyρ : [ equi ] Δ ⊢ⁿ ρ ∈ Γ) →
    unerase-tmsub (weakenAll-⊢tmTm {b = b} tyρ) ≡ map weakenTmTm (unerase-tmsub tyρ)
unerase-tmsub-weakenAll-⊢tmTm [] = refl
unerase-tmsub-weakenAll-⊢tmTm (ty ∷ tyρ) = cong₂ _∷_ (unerase-weaken-⊢tmTm ty) (unerase-tmsub-weakenAll-⊢tmTm tyρ)

unerase-/⊢tm : ∀ {m n k} {Γ : Ctx m n} {Δ : Ctx k n} {t a ρ} →
                (ty : [ equi ] Γ ⊢ t ∈ a) → (tyρ : [ equi ] Γ ⇒ Δ ⊢ ρ) →
                unerase (ty /⊢tm tyρ) ≡ unerase ty /tm unerase-tmsub tyρ
unerase-/⊢tm (var x) tyρ = unerase-lookup-⊢ x tyρ
unerase-/⊢tm (Λ ty) tyρ = cong Λ (
                          trans (unerase-/⊢tm ty (weakenAll-⊢tmTp tyρ))
                          (cong (unerase ty /tm_) (unerase-tmsub-weakenAll-⊢tmTp tyρ)))
unerase-/⊢tm (λ' a ty) tyρ =
  cong (λ' a) (
    trans (unerase-/⊢tm ty (tyρ ↑⊢tm))
      (cong (unerase ty /tm_) (cong (var zero ∷_) (unerase-tmsub-weakenAll-⊢tmTm tyρ))))
unerase-/⊢tm (ty [ b ]) tyρ = cong (_[ b ]) (unerase-/⊢tm ty tyρ)
unerase-/⊢tm (ty₁ · ty₂) tyρ = cong₂ _·_ (unerase-/⊢tm ty₁ tyρ) (unerase-/⊢tm ty₂ tyρ)
unerase-/⊢tm (fold a ty) tyρ = cong (fold a) (unerase-/⊢tm ty tyρ)
unerase-/⊢tm (unfold a ty) tyρ = cong (unfold a) (unerase-/⊢tm ty tyρ)

unerase-[/⊢tmTm] : ∀ {t₁ : Term 1 0} {t₂ : Term 0 0} {τ₁ τ₂}
                  (ty₁ : [ equi ] τ₁ ∷ [] ⊢ t₁ ∈ τ₂) →
                  (ty₂ : [ equi ] [] ⊢ t₂ ∈ τ₁) →
                  unerase (ty₁ [/⊢tmTm ty₂ ]) ≡ unerase ty₁ [/tmTm unerase ty₂ ]
unerase-[/⊢tmTm] ty₁ ty₂ = unerase-/⊢tm ty₁ (sub-⊢tmTm ty₂)

unerase-eval : ∀ {t₁ t₂ : Term 0 0} {τ : Type 0}→
                {ty₁ : [ equi ] [] ⊢ t₁ ∈ τ} → {ty₂ : [ equi ] [] ⊢ t₂ ∈ τ} →
                ty₁ ⟶d ty₂ →
                unerase ty₁ ⟶t unerase ty₂
unerase-eval (beta {a = a} ty₁ ty₂ vty₂) =
  subst₂ _⟶t_ (cong (λ' _ _ ·_)
    (sym (unerase-vty vty₂)))
    (trans (cong (λ t → unerase ty₁ [/tmTm t ]) (sym (unerase-vty vty₂))) (sym (unerase-[/⊢tmTm] ty₁ ty₂)))
    beta
unerase-eval (app₁ eval) = app₁ (unerase-eval eval)
unerase-eval (app₂ {ty₂ = ty₂} {ty₂′ = ty₂′} vty₁ eval) =
  subst₂ (λ t₁ t₁′ → (t₁ · unerase ty₂) ⟶t (t₁′ · unerase ty₂′))
    (sym (unerase-vty vty₁))
    (sym (unerase-vty vty₁))
    (app₂ (unerase-eval eval))
unerase-eval (Beta {ty = ty} {b = τ}) =
  subst ((Λ (unerase ty) [ τ ]) ⟶t_) (sym (unerase-[/⊢tmTp] ty τ)) Beta
unerase-eval (App eval) = App (unerase-eval eval)
unerase-eval (unfoldFold vty₂) =
  subst₂ _⟶t_
    (sym (cong (λ t → unfold _ (fold _ t)) (unerase-vty vty₂)))
    (sym (unerase-vty vty₂))
    unfoldFold
unerase-eval (fold eval) = fold (unerase-eval eval)
unerase-eval (unfold eval) = unfold (unerase-eval eval)

unerase-eval* : ∀ {t₁ t₂ : Term 0 0} {τ : Type 0}→
                {ty₁ : [ equi ] [] ⊢ t₁ ∈ τ} → {ty₂ : [ equi ] [] ⊢ t₂ ∈ τ} →
                ty₁ ⟶d* ty₂ →
                unerase ty₁ ⟶t* unerase ty₂
unerase-eval* refl⟶d* = refl⟶t*
unerase-eval* (underlying⟶d* eval) = underlying⟶t* (unerase-eval eval)
unerase-eval* (trans⟶d* evals₁ evals₂) = trans⟶t* (unerase-eval* evals₁) (unerase-eval* evals₂)

erase-⇓-inv : {t : Term 0 0} {τ : Type 0} →
              [ iso ] [] ⊢ t ∈ τ →
              erase t ⇓ →
              t ⇓
erase-⇓-inv {t} {τ} ty (term v evals) = term (unerase-vderiv (normalizeDeriv-Value tyV)) evals′
  where tyV : [ equi ] [] ⊢ ⌜ v ⌝ ∈ τ
        tyV = preservation* (erase-ty ty) evals

        unerase-evals : unerase (erase-ty ty) ⟶t* unerase (preservation* (erase-ty ty) evals)
        unerase-evals = unerase-eval* (derivFollows* (erase-ty ty) evals)

        unerase-evals′ : t ⟶t* unerase (preservation* (erase-ty ty) evals)
        unerase-evals′ = subst (_⟶t* (unerase (preservation* (erase-ty ty) evals))) (unerase-erase ty) unerase-evals

        evals′ : t ⟶t* ⌜ unerase-vderiv (normalizeDeriv-Value tyV) ⌝
        evals′ = trans⟶t* unerase-evals′
                 (subst ((unerase (preservation* (erase-ty ty) evals)) ⟶t*_)
                   (unerase-vty (normalizeDeriv-Value tyV))
                   (unerase-eval* (normalizeDeriv-eval* tyV)))

unerase-⇓ : {t : Term 0 0} {τ : Type 0} →
            (ty : [ equi ] [] ⊢ t ∈ τ) →
            t ⇓ →
            unerase ty ⇓
unerase-⇓ {t} {τ} ty (term v evals) = term (unerase-vderiv (normalizeDeriv-Value tyV)) evals′
  where tyV : [ equi ] [] ⊢ ⌜ v ⌝ ∈ τ
        tyV = preservation* ty evals

        unerase-evals : unerase ty ⟶t* unerase (preservation* ty evals)
        unerase-evals = unerase-eval* (derivFollows* ty evals)

        evals′ : unerase ty ⟶t* ⌜ unerase-vderiv (normalizeDeriv-Value tyV) ⌝
        evals′ = trans⟶t* unerase-evals
                 (subst ((unerase (preservation* ty evals)) ⟶t*_)
                   (unerase-vty (normalizeDeriv-Value tyV))
                   (unerase-eval* (normalizeDeriv-eval* tyV)))


unerase-context : ∀ {mᵢ nᵢ mₒ nₒ} {C : Context mᵢ nᵢ mₒ nₒ}
                   {Γᵢ : Ctx mᵢ nᵢ} {τᵢ : Type nᵢ} {Γₒ : Ctx mₒ nₒ} {τₒ : Type nₒ} →
                   [ equi ]⊢ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ τₒ →
                   Context mᵢ nᵢ mₒ nₒ
unerase-context hole = hole
unerase-context (Λ tyC) = Λ (unerase-context tyC)
unerase-context (λ' a tyC) = λ' a (unerase-context tyC)
unerase-context (tyC [ τ ]) = unerase-context tyC [ τ ]
unerase-context (tyC ·₁ ty₂) = unerase-context tyC ·₁ unerase ty₂
unerase-context (ty₁ ·₂ tyC) = unerase ty₁ ·₂ unerase-context tyC
unerase-context (fold a tyC) = fold a (unerase-context tyC)
unerase-context (unfold a tyC) = unfold a (unerase-context tyC)


unerase-context-ty : ∀ {mᵢ nᵢ mₒ nₒ} {C : Context mᵢ nᵢ mₒ nₒ}
                   {Γᵢ : Ctx mᵢ nᵢ} {τᵢ : Type nᵢ} {Γₒ : Ctx mₒ nₒ} {τₒ : Type nₒ} →
                   (ty : [ equi ]⊢ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ τₒ) →
                   [ iso ]⊢ unerase-context ty ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ τₒ
unerase-context-ty hole = hole
unerase-context-ty (Λ tyC) = Λ (unerase-context-ty tyC)
unerase-context-ty (λ' a tyC) = λ' a (unerase-context-ty tyC)
unerase-context-ty (tyC [ τ ]) = unerase-context-ty tyC [ τ ]
unerase-context-ty (tyC ·₁ ty₂) = unerase-context-ty tyC ·₁ unerase-ty ty₂
unerase-context-ty (ty₁ ·₂ tyC) = unerase-ty ty₁ ·₂ unerase-context-ty tyC
unerase-context-ty (fold a tyC) = fold a (unerase-context-ty tyC)
unerase-context-ty (unfold a tyC) = unfold a (unerase-context-ty tyC)

erase-unerase-context : ∀ {mᵢ nᵢ mₒ nₒ} {C : Context mᵢ nᵢ mₒ nₒ}
                        {Γᵢ : Ctx mᵢ nᵢ} {τᵢ : Type nᵢ} {Γₒ : Ctx mₒ nₒ} {τₒ : Type nₒ} →
                        (tyC : [ equi ]⊢ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ τₒ) →
                        erase-context (unerase-context tyC) ≡ C
erase-unerase-context hole = refl
erase-unerase-context (Λ tyC) = cong Λ (erase-unerase-context tyC)
erase-unerase-context (λ' τ tyC) = cong (λ' τ) (erase-unerase-context tyC)
erase-unerase-context (tyC [ τ ]) = (cong (_[ τ ])) (erase-unerase-context tyC)
erase-unerase-context (tyC ·₁ ty₂) = cong₂ _·₁_ (erase-unerase-context tyC) (erase-unerase ty₂)
erase-unerase-context (ty₁ ·₂ tyC) = cong₂ _·₂_ (erase-unerase ty₁) (erase-unerase-context tyC)
erase-unerase-context (fold τ tyC) = erase-unerase-context tyC
erase-unerase-context (unfold τ tyC) = erase-unerase-context tyC

unerase-plug : ∀ {mᵢ nᵢ mₒ nₒ} {C : Context mᵢ nᵢ mₒ nₒ} {t}
               {Γᵢ : Ctx mᵢ nᵢ} {τᵢ : Type nᵢ} {Γₒ : Ctx mₒ nₒ} {τₒ : Type nₒ} →
               (tyC : [ equi ]⊢ C ∈ Γᵢ ∣ τᵢ ⇒ Γₒ ∣ τₒ) →
               (ty : [ equi ] Γᵢ ⊢ t ∈ τᵢ) →
               unerase (plug-ty tyC ty) ≡ plug (unerase-context tyC) (unerase ty)
unerase-plug hole ty = refl
unerase-plug (Λ tyC) ty = cong Λ (unerase-plug tyC ty)
unerase-plug (λ' τ tyC) ty = cong (λ' τ) (unerase-plug tyC ty)
unerase-plug (tyC [ τ ]) ty = cong (_[ τ ]) (unerase-plug tyC ty)
unerase-plug (tyC ·₁ ty₂) ty = cong (_· unerase ty₂) (unerase-plug tyC ty)
unerase-plug (ty₁ ·₂ tyC) ty = cong (unerase ty₁ ·_) (unerase-plug tyC ty)
unerase-plug (fold τ tyC) ty = cong (fold τ) (unerase-plug tyC ty)
unerase-plug (unfold τ tyC) ty = cong (unfold τ) (unerase-plug tyC ty)
