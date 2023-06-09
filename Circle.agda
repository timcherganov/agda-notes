module Circle where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool
open import Cubical.Relation.Nullary

data S¹ : Type where
  base : S¹
  loop : base ≡ base

-- The circle is nontrivial.

refl≢loop : ¬ refl ≡ loop
refl≢loop p = true≢false (congS f p)
  where
  S¹→Type : S¹ → Type
  S¹→Type base     = Bool
  S¹→Type (loop i) = notEq i

  f : base ≡ base → Bool
  f p = subst S¹→Type p true
