
\begin{code}

{-# OPTIONS --prop --rewriting #-}

open Agda.Primitive
open import Equality
open import Logic
open import Nat

module Integers where

-- The initial model for integers

module I where
  postulate
    Z       : Set
    Zero    : Z
    Suc     : Z → Z
    Pred    : Z → Z
    SucPred : ∀{i} → Suc (Pred i) ≡ i
    PredSuc : ∀{i} → Pred (Suc i) ≡ i

-- then the general definition of a model M :

\end{code}

We can define it using postulate like this

record Model {l} : Set (lsuc l) where
  field
    Z       : Set l
    Zero    : Z
    Suc     : Z → Z
    Pred    : Z → Z
    SucPred : ∀{i} → Suc (Pred i) ≡ i
    PredSuc : ∀{i} → Pred (Suc i) ≡ i
  postulate
    ⟦_⟧    : I.Z → Z
    ⟦Zero⟧ : ⟦ I.Zero ⟧ ≡ Zero
    ⟦Suc⟧  : ∀{i} → ⟦ I.Suc i ⟧ ≡ Suc ⟦ i ⟧
    ⟦Pred⟧ : ∀{i} → ⟦ I.Pred i ⟧ ≡ Pred ⟦ i ⟧

But it could be better to define first the general version : Dependent Model
And then extract the model from this definition :

\begin{code}

record DepModel {l} : Set (lsuc l) where
  field
    Z•       : I.Z -> Set l
    Zero•    : Z• I.Zero
    Suc•     : ∀{i} → Z• i → Z• (I.Suc i)
    Pred•    : ∀{i} → Z• i → Z• (I.Pred i)
    SucPred• : ∀{i} → (i• : Z• i) → transp⟨ Z• ⟩ I.SucPred (Suc• (Pred• i•)) ≡ i•
    PredSuc• : ∀{i} → (i• : Z• i) → transp⟨ Z• ⟩ I.PredSuc (Pred• (Suc• i•)) ≡ i•
  postulate
    ind : (i : I.Z) → Z• i
    indZero : ind(I.Zero) ≡ Zero•
    indSuc : ∀{i} → ind(I.Suc i) ≡ Suc• (ind i)
    indPred : ∀{i} → ind(I.Pred i) ≡ Pred• (ind i)
    {-# REWRITE indZero indSuc indPred #-}

-- Then the model is define as follow :

record Model {l} : Set (lsuc l) where
  field
    Z       : Set l
    Zero    : Z
    Suc     : Z → Z
    Pred    : Z → Z
    SucPred : ∀{i} → Suc (Pred i) ≡ i
    PredSuc : ∀{i} → Pred (Suc i) ≡ i
  ModelRec : DepModel
  ModelRec = record
    { Z• = λ _ → Z
    ; Zero• = Zero
    ; Suc• = Suc
    ; Pred• = Pred
    ; SucPred• = λ {i} i• → transpEq {_}{I.Z}{_}{_}{I.Suc (I.Pred i)}{i}{I.SucPred} SucPred
    ; PredSuc• = λ {i} i• → transpEq {_}{I.Z}{_}{_}{I.Pred (I.Suc i)}{i}{I.PredSuc} PredSuc
    }
  module ModelRec = DepModel ModelRec
  ⟦_⟧    : I.Z → Z
  ⟦_⟧    = ModelRec.ind
  ⟦Zero⟧ : ⟦ I.Zero ⟧ ≡ Zero
  ⟦Zero⟧ = refl
  ⟦Suc⟧  : ∀{i} → ⟦ I.Suc i ⟧ ≡ Suc ⟦ i ⟧
  ⟦Suc⟧  = refl
  ⟦Pred⟧ : ∀{i} → ⟦ I.Pred i ⟧ ≡ Pred ⟦ i ⟧
  ⟦Pred⟧ = refl

-- The model is usefull for its recursor :
  -- it let us define functions using pattern matching
  -- and force us to verify that the relation is compatible with the function

-- As example the addition :

addTo : I.Z → Model
addTo a = record
  { Z       = I.Z
  ; Zero    = a
  ; Suc     = I.Suc
  ; Pred    = I.Pred
  ; SucPred = I.SucPred
  ; PredSuc = I.PredSuc
  }
module addTo a = Model (addTo a)

_+_ : I.Z → I.Z → I.Z
i + j = addTo.⟦_⟧ j i
infix 5 _+_

\end{code}

Using induction (DepModel) we can prove some properites like :
  - existence of a neutral element for addition
  - associativity of addition
  - comutativity of addition
  - existence of an inverse
  - ...

It can be simplier to definie a special model for proof :
Because we use Prop, there is unicity of the element of a type Prop (UIP)
then the cases SucPred• and PredSuc• are redondent :

\begin{code}

record DepProof {l} : Set (lsuc l) where
  field
    Z•      : I.Z → Prop l
    Zero•   : Z• I.Zero
    Suc•    : ∀{i} → (i• : Z• i) → Z• (I.Suc i)
    Pred•    : ∀{i} → Z• i → Z• (I.Pred i)
  DepModelProof : DepModel
  DepModelProof = record
    { Z•       = λ i → Lift (Z• i)
    ; Zero•    = ⟪ Zero• ⟫
    ; Suc•     = λ i• → ⟪ Suc• (unfold i•) ⟫
    ; Pred•    = λ i• → ⟪ Pred• (unfold i•) ⟫
    ; SucPred• = λ _ → refl
    ; PredSuc• = λ _ → refl
    }
  module DepModelProof = DepModel DepModelProof
  ind : (i : I.Z) → Z• i
  ind i = unfold (DepModelProof.ind i)

-- Addition Associativity

+assocProof : I.Z → I.Z → DepProof
+assocProof b c = record
  { Z•       = λ a → (a + b) + c ≡ a + (b + c)
  ; Zero•    = refl
  ; Suc•     = λ HR → cong⟨ I.Suc ⟩ HR
  ; Pred•    = λ HR → cong⟨ I.Pred ⟩ HR
  }

+assoc : (a b c : I.Z) → (a + b) + c ≡ a + (b + c)
+assoc a b c = DepProof.ind (+assocProof b c) a

-- Neutral Element for Addition

+NeutralRightProof : DepProof
+NeutralRightProof = record
  { Z•       = λ i → (i + I.Zero) ≡ i
  ; Zero•    = refl
  ; Suc•     = λ HR → cong⟨ I.Suc ⟩ HR
  ; Pred•    = λ HR → cong⟨ I.Pred ⟩ HR
  }

+Neutral : (i : I.Z) → ((i + I.Zero) ≡ i) ∧ ((I.Zero + i) ≡ i)
+Neutral i = DepProof.ind +NeutralRightProof i ,
             refl

-- Commutativity of addition

+commLemmaSucProof : I.Z → DepProof
+commLemmaSucProof b = record
 { Z• = λ a → (I.Suc a) + b ≡ a + (I.Suc b)
 ; Zero•    = refl
 ; Suc•     = λ HR     → cong⟨ I.Suc ⟩ HR
 ; Pred•    = λ {a} HR → (I.Suc (I.Pred a)) + b ≡⟨ I.SucPred ⟩
                         a + b                  ≡⟨ symetry I.PredSuc ⟩
                         (cong⟨ I.Pred ⟩ HR)
 }

+commLemmaSuc : (a b : I.Z) → (I.Suc a) + b ≡ a + (I.Suc b)
+commLemmaSuc a b = DepProof.ind (+commLemmaSucProof b) a

+commLemmaPredProof : I.Z → DepProof
+commLemmaPredProof b = record
 { Z• = λ a → (I.Pred a) + b ≡ a + (I.Pred b)
 ; Zero• = refl
 ; Suc•  = λ {a} HR → (I.Pred (I.Suc a)) + b ≡⟨ I.PredSuc ⟩
                      a + b                  ≡⟨ symetry I.SucPred ⟩
                      (cong⟨ I.Suc ⟩ HR)
 ; Pred• = λ HR     → cong⟨ I.Pred ⟩ HR
 }

+commLemmaPred : (a b : I.Z) → (I.Pred a) + b ≡ a + (I.Pred b)
+commLemmaPred a b = DepProof.ind (+commLemmaPredProof b) a

+commProof : I.Z → DepProof
+commProof b = record
  { Z•    = λ a → a + b ≡ b + a
  ; Zero• = symetry (DepProof.ind +NeutralRightProof b)
  ; Suc•  = λ {a} HR → (I.Suc a) + b ≡⟨ cong⟨ I.Suc ⟩ HR ⟩ (+commLemmaSuc b a)
  ; Pred• = λ {a} HR → (I.Pred a) + b ≡⟨ cong⟨ I.Pred ⟩ HR ⟩ (+commLemmaPred b a)
  }

+comm : (a b : I.Z) → a + b ≡ b + a
+comm a b = DepProof.ind (+commProof b) a

-- Inverse for Addition

negation : Model
negation = record
  { Z = I.Z
  ; Zero = I.Zero
  ; Suc = λ i → I.Pred i
  ; Pred = λ i → I.Suc i
  ; SucPred = I.PredSuc
  ; PredSuc = I.SucPred
  }
module negation = Model negation

-_ : I.Z → I.Z
-_ = negation.⟦_⟧

+InverseProof : DepProof
+InverseProof = record
  { Z• = λ i → - i + i ≡ I.Zero
  ; Zero• = refl 
  ; Suc•  = λ {i} HR → - (I.Suc i) + (I.Suc i) ≡⟨ cong⟨ I.Pred ⟩ (symetry (+commLemmaSuc (- i) i)) ⟩
                        I.Pred (I.Suc (- i + i)) ≡⟨ I.PredSuc ⟩ HR
  ; Pred• = λ {i} HR → - (I.Pred i) + (I.Pred i) ≡⟨ cong⟨ I.Suc ⟩ (symetry (+commLemmaPred (- i) i)) ⟩
                        I.Suc (I.Pred (- i + i)) ≡⟨ I.SucPred ⟩ HR
  }

+inverse : (i : I.Z) → (- i + i ≡ I.Zero)
+inverse i = DepProof.ind +InverseProof i

-- We can go further and introduce the multiplication to show that (Z, +, ×) is a ring

multTo : I.Z → Model
multTo a = record
  { Z       = I.Z
  ; Zero    = I.Zero
  ; Suc     = λ b → a + b
  ; Pred    = λ b → - a + b
  ; SucPred = λ {i} → a + ((- a) + i)  ≡⟨ symetry (+assoc a (- a) i) ⟩
                      (a + (- a)) + i  ≡⟨ (cong⟨ (λ x → x + i) ⟩) (+comm a (- a)) ⟩
                      (- a + a) + i    ≡⟨ (cong⟨ (λ x → x + i) ⟩) (+inverse a) ⟩
                      refl
  ; PredSuc = λ {i} → (- a) + (a + i)  ≡⟨ symetry (+assoc (- a) a i) ⟩
                      (- a + a) + i    ≡⟨ (cong⟨ (λ x → x + i) ⟩) (+inverse a) ⟩
                      refl                 
  }
module multTo a = Model (multTo a)

_×_ : I.Z → I.Z → I.Z
i × j = multTo.⟦_⟧ j i
infix 6 _×_

-- Distributivity Left and Right

×distribLeftProof : I.Z → I.Z → DepProof
×distribLeftProof b c = record
  { Z• = λ a → (a + b) × c ≡ a × c + b × c
  ; Zero• = refl
  ; Suc•  = λ {a} HR → c + (a + b) × c     ≡⟨ cong⟨ (λ x → c + x) ⟩ HR ⟩ (symetry (+assoc c (a × c) (b × c)))
  ; Pred• = λ {a} HR → (- c) + (a + b) × c ≡⟨ cong⟨ (λ x → - c + x) ⟩ HR ⟩ (symetry (+assoc (- c) (a × c) (b × c)))
  }

×distribLeft : (a b c : I.Z) → (a + b) × c ≡ a × c + b × c 
×distribLeft a b c = DepProof.ind (×distribLeftProof b c) a

×-1distribRightProof : I.Z → DepProof
×-1distribRightProof b = record
  { Z• = λ a → - (a + b) ≡ (- a) + (- b)
  ; Zero• = refl
  ; Suc•  = λ HR → cong⟨ I.Pred ⟩ HR
  ; Pred• = λ HR → cong⟨ I.Suc ⟩ HR
  }

×-1distribRight : (a b : I.Z) → - (a + b) ≡ (- a) + (- b)
×-1distribRight a b = DepProof.ind (×-1distribRightProof b) a

×distribRightProof : I.Z → I.Z → DepProof
×distribRightProof b c = record
  { Z• = λ a → a × (b + c) ≡ a × b + a × c
  ; Zero• = refl
  ; Suc•  = λ {a} HR → (b + c) + a × (b + c)     ≡⟨ cong⟨ (λ x → (b + c) + x) ⟩ HR ⟩
                       (b + c) + (a × b + a × c) ≡⟨ +assoc b c (a × b + a × c) ⟩
                       b + (c + (a × b + a × c)) ≡⟨ cong⟨ (λ x → b + x) ⟩ (symetry (+assoc c (a × b) (a × c))) ⟩
                       b + ((c + a × b) + a × c) ≡⟨ cong⟨ (λ x → b + (x + a × c)) ⟩ (+comm c (a × b)) ⟩
                       b + ((a × b + c) + a × c) ≡⟨ cong⟨ (λ x → b + x) ⟩ (+assoc (a × b) c (a × c)) ⟩
                       b + (a × b + (c + a × c)) ≡⟨ symetry (+assoc b (a × b) (c + a × c)) ⟩
                       refl
  ; Pred• = λ {a} HR → (- (b + c)) + a × (b + c)          ≡⟨ cong⟨ (λ x → (- (b + c )) + x) ⟩ HR ⟩
                       (- (b + c)) + (a × b + a × c)      ≡⟨ cong⟨ (λ x → x + (a × b + a × c)) ⟩ (×-1distribRight b c) ⟩
                       ((- b) + (- c)) + (a × b + a × c)  ≡⟨ +assoc (- b) (- c) (a × b + a × c) ⟩
                       (- b) + ((- c) + (a × b + a × c))  ≡⟨ cong⟨ (λ x → (- b) + x) ⟩ (symetry (+assoc (- c) (a × b) (a × c))) ⟩
                       (- b) + (((- c) + a × b) + a × c)  ≡⟨ cong⟨ (λ x → (- b) + (x + a × c)) ⟩ (+comm (- c) (a × b)) ⟩
                       (- b) + ((a × b + (- c)) + a × c)  ≡⟨ cong⟨ (λ x → (- b) + x) ⟩ (+assoc (a × b) (- c) (a × c)) ⟩
                       (- b) + (a × b + ((- c) + a × c))  ≡⟨ symetry (+assoc (- b) (a × b) ((- c) + a × c)) ⟩
                       refl
  }

×distribRight : (a b c : I.Z) → a × (b + c) ≡ a × b + a × c 
×distribRight a b c = DepProof.ind (×distribRightProof b c) a

-1uniPotProof : DepProof
-1uniPotProof = record
  { Z• = λ a → - (- a) ≡ a
  ; Zero• = refl
  ; Suc•  = λ HR → cong⟨ I.Suc ⟩ HR
  ; Pred• = λ HR → cong⟨ I.Pred ⟩ HR
  }

-1uniPot : (a : I.Z) → - (- a) ≡ a
-1uniPot a = DepProof.ind -1uniPotProof a

-- Associativity for multiplication

×-1assocProof : I.Z → DepProof
×-1assocProof b = record
  { Z• = λ a → (- a) × b ≡ - (a × b)
  ; Zero• = refl
  ; Suc•  = λ {a} HR → (- b + (- a) × b)       ≡⟨ cong⟨ (λ x → - b + x) ⟩ HR ⟩
                       (- b + (- (a × b)))     ≡⟨ symetry (×-1distribRight b (a × b)) ⟩
                       refl
  ; Pred• = λ {a} HR → b + (- a) × b           ≡⟨ cong⟨ (λ x → b + x) ⟩ HR ⟩
                       b + (- (a × b))         ≡⟨ cong⟨ (λ x → x + (- (a × b))) ⟩ (symetry (-1uniPot b)) ⟩
                       (- (- b)) + (- (a × b)) ≡⟨ symetry (×-1distribRight (- b) (a × b)) ⟩
                       refl
  }

×-1assoc : (a b : I.Z) → (- a) × b ≡ - (a × b)
×-1assoc a b = DepProof.ind (×-1assocProof b) a

×assocProof : I.Z → I.Z → DepProof
×assocProof b c = record
  { Z• = λ a → (a × b) × c ≡ a × (b × c)
  ; Zero• = refl
  ; Suc•  = λ {a} HR → (b + a × b) × c ≡⟨ ×distribLeft b (a × b) c ⟩ (cong⟨ (λ x → b × c + x) ⟩ HR )
  ; Pred• = λ {a} HR → (- b + a × b) × c       ≡⟨ ×distribLeft (- b) (a × b) c ⟩
                       (- b) × c + (a × b) × c ≡⟨ cong⟨ (λ x → (- b) × c + x) ⟩ HR ⟩
                       (- b) × c + a × (b × c) ≡⟨ cong⟨ (λ x → x + a × (b × c)) ⟩ (×-1assoc b c) ⟩
                       refl
  }

\end{code}

--------------------------------------------------

We want now to proof normalisation of QIIT integers :
  - describe the normal form
    (model without equalities)
  - prove the inclusion
    (every normal form is actually an integer)
  - prove the normalisation
    (every integers has a normal form
  - thoses two steps are homomorphism
  - thoses are both stable

\begin{code}

-- Normal Forms

data NFZ : Set where
  -Nat : ℕ → NFZ
  Zero : NFZ
  +Nat : ℕ → NFZ

-- Inclusion

⌜_⌝ : NFZ → I.Z
⌜ -Nat zero ⌝     = I.Pred I.Zero
⌜ -Nat (succ i) ⌝ = I.Pred ⌜ -Nat i ⌝
⌜ Zero ⌝          = I.Zero
⌜ +Nat zero ⌝     = I.Suc I.Zero
⌜ +Nat (succ i) ⌝ = I.Suc ⌜ +Nat i ⌝

-- Normalisation

NormModel : Model
NormModel = record
  { Z = NFZ
  ; Zero    = Zero
  ; Suc     = λ { ( -Nat zero     ) → Zero
                ; ( -Nat (succ i) ) → -Nat i
                ; ( Zero          ) → +Nat zero
                ; ( +Nat i        ) → +Nat (succ i)
                }
  ; Pred    = λ { ( -Nat i        ) → -Nat (succ i)
                ; ( Zero          ) → -Nat zero
                ; ( +Nat zero     ) → Zero
                ; ( +Nat (succ i) ) → +Nat i
                }
  ; SucPred = λ { { -Nat zero     } → refl
                ; { -Nat (succ i) } → refl
                ; { Zero          } → refl
                ; { +Nat zero     } → refl
                ; { +Nat (succ i) } → refl
                }
  ; PredSuc = λ { { -Nat zero     } → refl
                ; { -Nat (succ i) } → refl
                ; { Zero          } → refl
                ; { +Nat zero     } → refl
                ; { +Nat (succ i) } → refl
                }
  }

module NormModel = Model NormModel

norm : I.Z → NFZ
norm = NormModel.⟦_⟧

-- Homomorphism

normZeroMorph : ⌜ NormModel.Zero ⌝ ≡ I.Zero
normZeroMorph = refl

normSucMorph : (nf : NFZ) → ⌜ NormModel.Suc nf ⌝ ≡ I.Suc ⌜ nf ⌝
normSucMorph = λ { ( -Nat zero     ) → symetry I.SucPred
                 ; ( -Nat (succ i) ) → symetry I.SucPred
                 ; ( Zero          ) → refl
                 ; ( +Nat x        ) → refl
                 }

normPredMorph : (nf : NFZ) → ⌜ NormModel.Pred nf ⌝ ≡ I.Pred ⌜ nf ⌝
normPredMorph = λ { ( -Nat x        ) → refl
                  ; ( Zero          ) → refl
                  ; ( +Nat zero     ) → symetry I.PredSuc
                  ; ( +Nat (succ i) ) → symetry I.PredSuc
                  }

-- norm is stable by definition (recursor for a I.Z model)

-- Stability

NormStability : (nf : NFZ) → norm ⌜ nf ⌝ ≡ nf
NormStability (-Nat zero) =
  refl
NormStability (-Nat (succ i)) =
  cong⟨ NormModel.Pred ⟩ (NormStability (-Nat i))
NormStability Zero =
  refl
NormStability (+Nat zero) =
  refl
NormStability (+Nat (succ i)) =
  cong⟨ NormModel.Suc ⟩ (NormStability (+Nat i))

InclusionStabilityProof : DepProof
InclusionStabilityProof = record
  { Z•       = λ i → ⌜ norm i ⌝ ≡ i
  ; Zero•    = refl
  ; Suc•     = λ {i} i• → ⌜ norm (I.Suc i) ⌝ ≡⟨ normSucMorph (norm i) ⟩ (cong⟨ I.Suc ⟩ i•)
  ; Pred•    = λ {i} i• → ⌜ norm (I.Pred i) ⌝ ≡⟨ normPredMorph (norm i) ⟩ (cong⟨ I.Pred ⟩ i•)
  }

InclusionStability : (i : I.Z) → ⌜ norm i ⌝ ≡ i
InclusionStability i = DepProof.ind InclusionStabilityProof i

\end{code}
