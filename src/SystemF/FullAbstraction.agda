module SystemF.FullAbstraction where

open import SystemF.Term
open import SystemF.Type
open import SystemF.WtTerm
open import SystemF.IsoEquiLink
open import SystemF.Contexts
open import SystemF.DerivationSemantics
open import SystemF.ReductionJudgement
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; Equivalence; equivalence)
open import Relation.Binary.PropositionalEquality using (subst₂; subst; sym; trans; cong; cong₂)

erase-equivalence-reflection : ∀ {m n} {Γ : Ctx m n} {τ} {t₁ t₂ : Term m n} {ty₁ : [ iso ] Γ ⊢ t₁ ∈ τ} {ty₂ : [ iso ] Γ ⊢ t₂ ∈ τ} →
            [ equi ] Γ ⊢ erase t₁ ∣ erase-ty ty₁ ≈c erase t₂ ∣ erase-ty ty₂ ∶ τ →
            [ iso ] Γ ⊢ t₁ ∣ ty₁ ≈c t₂ ∣ ty₂ ∶ τ
erase-equivalence-reflection {t₁ = t₁} {t₂} {ty₁} {ty₂} eq {C} {τ′} tyC =
  equivalence to from
  where to : plug C t₁ ⇓ → plug C t₂ ⇓
        to tm₁ = step₃
          where
            step₁ : plug (erase-context C) (erase t₁) ⇓
            step₁ = subst _⇓ (erase-plug C) (erase-⇓ tm₁)

            equiv : plug (erase-context C) (erase t₁) ⇓ ⇔ plug (erase-context C) (erase t₂) ⇓
            equiv = eq (erase-context-ty tyC)

            step₂ : plug (erase-context C) (erase t₂) ⇓
            step₂ = Equivalence.to equiv ⟨$⟩ step₁

            step₂′ : erase (plug C t₂) ⇓
            step₂′ = subst _⇓ (sym (erase-plug C)) step₂

            step₃ : plug C t₂ ⇓
            step₃ = erase-⇓-inv (plug-ty tyC ty₂) step₂′

        from : plug C t₂ ⇓ → plug C t₁ ⇓
        from tm₂ = step₃
          where
            step₁ : plug (erase-context C) (erase t₂) ⇓
            step₁ = subst _⇓ (erase-plug C) (erase-⇓ tm₂)

            equiv : plug (erase-context C) (erase t₁) ⇓ ⇔ plug (erase-context C) (erase t₂) ⇓
            equiv = eq (erase-context-ty tyC)

            step₂ : plug (erase-context C) (erase t₁) ⇓
            step₂ = Equivalence.from equiv ⟨$⟩ step₁

            step₂′ : erase (plug C t₁) ⇓
            step₂′ = subst _⇓ (sym (erase-plug C)) step₂

            step₃ : plug C t₁ ⇓
            step₃ = erase-⇓-inv (plug-ty tyC ty₁) step₂′


erase-equivalence-preservation : ∀ {m n} {Γ : Ctx m n} {τ} {t₁ t₂ : Term m n} {ty₁ : [ iso ] Γ ⊢ t₁ ∈ τ} {ty₂ : [ iso ] Γ ⊢ t₂ ∈ τ} →
                           [ iso ] Γ ⊢ t₁ ∣ ty₁ ≈c t₂ ∣ ty₂ ∶ τ →
                           [ equi ] Γ ⊢ erase t₁ ∣ erase-ty ty₁ ≈c erase t₂ ∣ erase-ty ty₂ ∶ τ
erase-equivalence-preservation {t₁ = t₁} {t₂} {ty₁} {ty₂} eq {C} {τ′} tyC =
  equivalence to from
  where to : plug C (erase t₁) ⇓ → plug C (erase t₂) ⇓
        to tm₁ = step₃
          where
            step₁ : plug (unerase-context tyC) t₁ ⇓
            step₁ = subst _⇓
                      (trans (unerase-plug tyC (erase-ty ty₁))
                        (cong (plug (unerase-context tyC)) (unerase-erase ty₁)))
                      (unerase-⇓ (plug-ty tyC (erase-ty ty₁)) tm₁)

            equiv : plug (unerase-context tyC) t₁ ⇓ ⇔ plug (unerase-context tyC) t₂ ⇓
            equiv = eq (unerase-context-ty tyC)

            step₂ : plug (unerase-context tyC) t₂ ⇓
            step₂ = Equivalence.to equiv ⟨$⟩ step₁

            step₃ : plug C (erase t₂) ⇓
            step₃ = subst _⇓
                          (trans (erase-plug (unerase-context tyC))
                            (cong (λ C → plug C (erase t₂)) (erase-unerase-context tyC)))
                          (erase-⇓ step₂)

        from : plug C (erase t₂) ⇓ → plug C (erase t₁) ⇓
        from tm₂ = step₃
          where
            step₁ : plug (unerase-context tyC) t₂ ⇓
            step₁ = subst _⇓
                      (trans (unerase-plug tyC (erase-ty ty₂))
                        (cong (plug (unerase-context tyC)) (unerase-erase ty₂)))
                      (unerase-⇓ (plug-ty tyC (erase-ty ty₂)) tm₂)

            equiv : plug (unerase-context tyC) t₁ ⇓ ⇔ plug (unerase-context tyC) t₂ ⇓
            equiv = eq (unerase-context-ty tyC)

            step₂ : plug (unerase-context tyC) t₁ ⇓
            step₂ = Equivalence.from equiv ⟨$⟩ step₁

            step₃ : plug C (erase t₁) ⇓
            step₃ = subst _⇓
                          (trans (erase-plug (unerase-context tyC))
                            (cong (λ C → plug C (erase t₁)) (erase-unerase-context tyC)))
                          (erase-⇓ step₂)

unerase-equivalence-preservation : ∀ {m n} {Γ : Ctx m n} {τ} {t₁ t₂ : Term m n} {ty₁ : [ equi ] Γ ⊢ t₁ ∈ τ} {ty₂ : [ equi ] Γ ⊢ t₂ ∈ τ} →
            [ equi ] Γ ⊢ t₁ ∣ ty₁ ≈c t₂ ∣ ty₂ ∶ τ →
            [ iso ] Γ ⊢ unerase ty₁ ∣ unerase-ty ty₁ ≈c unerase ty₂ ∣ unerase-ty ty₂ ∶ τ
unerase-equivalence-preservation {t₁ = t₁} {t₂} {ty₁} {ty₂} eq {C} {τ′} tyC =
  equivalence to from
  where to : plug C (unerase ty₁) ⇓ → plug C (unerase ty₂) ⇓
        to tm₁ = step₃
          where
            step₁ : plug (erase-context C) t₁ ⇓
            step₁ = subst _⇓ (
                      trans (erase-plug C)
                        (cong (plug (erase-context C)) (erase-unerase ty₁))) (erase-⇓ tm₁)

            equiv : plug (erase-context C) t₁ ⇓ ⇔ plug (erase-context C) t₂ ⇓
            equiv = eq (erase-context-ty tyC)

            step₂ : plug (erase-context C) t₂ ⇓
            step₂ = Equivalence.to equiv ⟨$⟩ step₁

            step₂′ : erase (plug C (unerase ty₂)) ⇓
            step₂′ = subst _⇓ (
                       trans (cong (plug (erase-context C)) (sym (erase-unerase ty₂)))
                         (sym (erase-plug C))) step₂

            step₃ : plug C (unerase ty₂) ⇓
            step₃ = erase-⇓-inv (plug-ty tyC (unerase-ty ty₂)) step₂′

        from : plug C (unerase ty₂) ⇓ → plug C (unerase ty₁) ⇓
        from tm₂ = step₃
          where
            step₁ : plug (erase-context C) t₂ ⇓
            step₁ = subst _⇓ (
                      trans (erase-plug C)
                        (cong (plug (erase-context C)) (erase-unerase ty₂))) (erase-⇓ tm₂)

            equiv : plug (erase-context C) t₁ ⇓ ⇔ plug (erase-context C) t₂ ⇓
            equiv = eq (erase-context-ty tyC)

            step₂ : plug (erase-context C) t₁ ⇓
            step₂ = Equivalence.from equiv ⟨$⟩ step₁

            step₂′ : erase (plug C (unerase ty₁)) ⇓
            step₂′ = subst _⇓ (
                       trans (cong (plug (erase-context C)) (sym (erase-unerase ty₁)))
                         (sym (erase-plug C))) step₂

            step₃ : plug C (unerase ty₁) ⇓
            step₃ = erase-⇓-inv (plug-ty tyC (unerase-ty ty₁)) step₂′


unerase-equivalence-reflection : ∀ {m n} {Γ : Ctx m n} {τ} {t₁ t₂ : Term m n} {ty₁ : [ equi ] Γ ⊢ t₁ ∈ τ} {ty₂ : [ equi ] Γ ⊢ t₂ ∈ τ} →
                               [ iso ] Γ ⊢ unerase ty₁ ∣ unerase-ty ty₁ ≈c unerase ty₂ ∣ unerase-ty ty₂ ∶ τ →
                               [ equi ] Γ ⊢ t₁ ∣ ty₁ ≈c t₂ ∣ ty₂ ∶ τ
unerase-equivalence-reflection {t₁ = t₁} {t₂} {ty₁} {ty₂} eq {C} {τ′} tyC =
  equivalence to from
  where to : plug C t₁ ⇓ → plug C t₂ ⇓
        to tm₁ = step₃
          where
            step₁ : plug (unerase-context tyC) (unerase ty₁) ⇓
            step₁ = subst _⇓
                      (unerase-plug tyC ty₁)
                      (unerase-⇓ (plug-ty tyC ty₁) tm₁)

            equiv : plug (unerase-context tyC) (unerase ty₁) ⇓ ⇔ plug (unerase-context tyC) (unerase ty₂) ⇓
            equiv = eq (unerase-context-ty tyC)

            step₂ : plug (unerase-context tyC) (unerase ty₂) ⇓
            step₂ = Equivalence.to equiv ⟨$⟩ step₁

            step₃ : plug C t₂ ⇓
            step₃ = subst _⇓
                          (trans (erase-plug (unerase-context tyC))
                            (cong₂ plug (erase-unerase-context tyC) (erase-unerase ty₂)))
                          (erase-⇓ step₂)

        from : plug C t₂ ⇓ → plug C t₁ ⇓
        from tm₂ = step₃
          where
            step₁ : plug (unerase-context tyC) (unerase ty₂) ⇓
            step₁ = subst _⇓
                      (unerase-plug tyC ty₂)
                      (unerase-⇓ (plug-ty tyC ty₂) tm₂)

            equiv : plug (unerase-context tyC) (unerase ty₁) ⇓ ⇔ plug (unerase-context tyC) (unerase ty₂) ⇓
            equiv = eq (unerase-context-ty tyC)

            step₂ : plug (unerase-context tyC) (unerase ty₁) ⇓
            step₂ = Equivalence.from equiv ⟨$⟩ step₁

            step₃ : plug C t₁ ⇓
            step₃ = subst _⇓
                          (trans (erase-plug (unerase-context tyC))
                            (cong₂ plug (erase-unerase-context tyC) (erase-unerase ty₁)))
                          (erase-⇓ step₂)
