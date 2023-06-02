module Choice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Foundations.Equiv.Properties using (hasSection)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism using (section)

open import Cubical.Functions.Surjection using (isSurjection)

open import Cubical.Data.Bool using (Bool; false; true; _≟_)
open import Cubical.Data.Unit using (Unit*; tt*)

open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; rec; map)
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/; squash/; []surjective; effective)

open import Cubical.Relation.Nullary using (¬_; Dec; Discrete; isPropDec; mapDec; sectionDiscrete)
open import Cubical.Relation.Binary using (Rel; module BinaryRelation)

-- The axiom of choice

AxiomOfChoice : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
AxiomOfChoice ℓ ℓ' = {X : Type ℓ} {Y : X → Type ℓ'} → isSet X →
  (∀ x → ∥ Y x ∥₁) → ∥ (∀ x → Y x) ∥₁

AxiomOfChoice' : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
AxiomOfChoice' ℓ ℓ' = {X : Type ℓ} {Y : Type ℓ'} {f : Y → X} → isSet X →
  isSurjection f → ∥ hasSection f ∥₁

AC→AC' : ∀ {ℓ ℓ'} → AxiomOfChoice ℓ (ℓ-max ℓ ℓ') → AxiomOfChoice' ℓ ℓ'
AC→AC' ac {f = f} HX Hf = map h (ac HX Hf)
  where
  h : (∀ x → fiber f x) → hasSection f
  h g = (λ x → fst (g x)) , (λ x → snd (g x))

AC'→AC : ∀ {ℓ ℓ'} → AxiomOfChoice' ℓ (ℓ-max ℓ ℓ') → AxiomOfChoice ℓ ℓ'
AC'→AC ac {X} {Y} HX ϕ = map h (ac HX sur)
  where
  f : Σ[ x ∈ X ] Y x → X
  f = fst

  sur : isSurjection f
  sur x = map (λ H → (x , H) , refl) (ϕ x)

  h : hasSection f → (∀ x → Y x)
  h (g , H) x = subst Y (H x) (snd (g x))

-- Excluded middle

ExcludedMiddle : ∀ ℓ → Type (ℓ-suc ℓ)
ExcludedMiddle ℓ = {P : Type ℓ} → isProp P → Dec P

-- The axiom of choice implies excluded middle

-- Let P be a mere proposition. By R denote the equivalence relation on Bool
-- defined by 'R true false = P'. Suppose f is the canonical surjection from
-- Bool to Bool/R, then 'f true ≡ f false' iff P. From the axiom of choice it
-- follows that f has a section. Then since Bool has decidable equality, so do
-- Bool/R. Hence 'f true ≡ f false' is decidable, and thus P is also
-- decidable.

private
  variable
    ℓ : Level

module RelOnBool (P : Type ℓ) where
  open BinaryRelation

  R : Rel Bool Bool ℓ
  R false false = Unit*
  R false true  = P
  R true  false = P
  R true  true  = Unit*

  isReflR : isRefl R
  isReflR false = tt*
  isReflR true  = tt*

  isSymR : isSym R
  isSymR false false H = H
  isSymR false true  H = H
  isSymR true  false H = H
  isSymR true  true  H = H

  isTransR : isTrans R
  isTransR false false _     _   Hbc = Hbc
  isTransR false true  false _   _   = tt*
  isTransR false true  true  Hab _   = Hab
  isTransR true  false false Hab _   = Hab
  isTransR true  false true  _   _   = tt*
  isTransR true  true  _     _   Hbc = Hbc

  isEquivRelR : isEquivRel R
  isEquivRelR = equivRel isReflR isSymR isTransR

  isPropValuedR : isProp P → isPropValued R
  isPropValuedR H false false = λ{ tt* tt* → refl }
  isPropValuedR H false true  = H
  isPropValuedR H true  false = H
  isPropValuedR H true  true  = λ{ tt* tt* → refl }

module _ (P : Type ℓ) where
  open RelOnBool P

  f : Bool → Bool / R
  f = [_]

  to : isProp P → f true ≡ f false → P
  to H = effective (isPropValuedR H) isEquivRelR true false

  from : P → f true ≡ f false
  from = eq/ true false

  from' : ¬ f true ≡ f false → ¬ P
  from' ¬p x = ¬p (from x)

  sec : AxiomOfChoice' ℓ ℓ-zero → ∥ hasSection f ∥₁
  sec ac = ac squash/ []surjective

  dec' : isProp P → hasSection f → Dec P
  dec' H (g , s) = mapDec (to H) from' d
    where
    discrete : Discrete (Bool / R)
    discrete = sectionDiscrete f g s _≟_

    d : Dec (f true ≡ f false)
    d = discrete (f true) (f false)

  dec : isProp P → ∥ hasSection f ∥₁ → Dec P
  dec H s = rec (isPropDec H) (dec' H) s

AC'→EM : AxiomOfChoice' ℓ ℓ-zero → ExcludedMiddle ℓ
AC'→EM ac H = dec _ H (sec _ ac)

AC→EM : AxiomOfChoice ℓ ℓ → ExcludedMiddle ℓ
AC→EM = AC'→EM ∘ AC→AC'
