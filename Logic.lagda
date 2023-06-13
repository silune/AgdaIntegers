\begin{code}

{-# OPTIONS --prop #-}

open import Agda.Primitive

module Logic where

  -- infixr 4 ⟨_,_⟩
  infixr 5 _∨_
  infixr 6 _∧_

  -- Unit type
  data ⊤ : Prop where
    triv : ⊤

  -- Empty type
  data ⊥ : Prop where

  -- Negation
  ¬ : Prop → Prop
  ¬ A = A → ⊥

  -- Conjunction
  data _∧_ (A B : Prop) : Prop where
    _,_ : A → B → A ∧ B

  -- Disjunction
  data _∨_ (A B : Prop) : Prop where
    left  : A → A ∨ B
    right : B → A ∨ B

  -- Existential Quantifier

  -- record ∃ {l}{A : Set l}{l'} (B : A → Prop l) : Prop (l ⊔ l') where
  --   constructor ⟨_,_⟩
  --   field
  --     pr₁ : A
  --     pr₂ : B (pr₁)
  -- open ∃ public

 \end{code}
