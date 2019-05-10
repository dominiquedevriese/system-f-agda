module SystemF.IsoEquiLink where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; cong₂)

open import SystemF.WtTerm
open import SystemF.Term
open import SystemF.Type
open import SystemF.Reduction


erase : ∀ {m n} → Term m n → Term m n
erase (var x) = var x
erase (Λ t) = Λ (erase t)
erase (λ' x t) = λ' x (erase t)
erase (μ x t) = μ x (erase t)
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
erase-ty (μ a ty) = μ a (erase-ty ty)
erase-ty (ty [ b ]) = erase-ty ty [ b ]
erase-ty (ty₁ · ty₂) = erase-ty ty₁ · erase-ty ty₂
erase-ty (fold a ty) = fold a (erase-ty ty)
erase-ty (unfold a ty) = unfold a (erase-ty ty)


unerase : ∀ {m n} {t : Term m n} {Γ : Ctx m n} {τ : Type n}→
           [ equi ] Γ ⊢ t ∈ τ →
           Term m n
unerase (var x) = var x
unerase (Λ ty) = Λ (unerase ty)
unerase (λ' a ty) = λ' a (unerase ty)
unerase (μ a ty) = μ a (unerase ty)
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
unerase-ty (μ a ty) = μ a (unerase-ty ty)
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
unerase-erase (μ a ty) = cong (μ a) (unerase-erase ty)
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
erase-unerase (μ a ty) = cong (μ a) (erase-unerase ty)
erase-unerase (ty [ b ]) = cong (λ t → t [ b ]) (erase-unerase ty)
erase-unerase (ty₁ · ty₂) = cong₂ _·_ (erase-unerase ty₁) (erase-unerase ty₂)
erase-unerase (fold a ty) = erase-unerase ty
erase-unerase (unfold a ty) = erase-unerase ty

