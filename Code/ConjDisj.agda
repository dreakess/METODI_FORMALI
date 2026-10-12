module Code.ConjDisj where

open import Library.Nat
open import Library.Fun



-- le presenteremo come la logica intuizionista

-- nozione di validità intesa in maniera diversa, attraverso il significato di proposizioni


-- qual'è il tipo delle prop. in agda?

-- che si chiama Prop = Set = Type

-- paradigma secondo cui :
-- I tipi sono Prop. e i termini dei tipi sono dimostrazioni

-- ∀ x . R(x, f(x)) → R(x, f(x))

-- il significato di una formuala è quella di essere vera o falsa

-- Nella semantica BHK delle proposizoni logiche si ha che

-- A : Set è intuizionisticamente valida se ∃ un' evidenza e : A

-- Evidenza? concetto primitivo come le rette, i piani

-- implicazione: A → B (quand'è che ha un Evidenza?) dove f è una trasformazione tale che, dato a : A si ottiene f a : B

-- intepretazione funzionale del concetto Evidenza


-- Prop. che dipende da x 
-- Quant. universale: ∀(x : A) → B x se per ogni a : A sia f a : B a dove B : A → Set

-- implicazione e quant. unviersale hanno la stessa intepretazione 

-- eguaglianza : e : t == s (t, s : termini)
-- e è un Evidenza di quello se e è una derivazione della logica equazionale di t == s


-- Congiunzione

data _∧_ (A B : Set) : Set where  -- -> si scrive /and
     _,_ : A → B → A ∧ B
     


infixr 3 _∧_
infixr 4 _,_

-- ∧ tipo di dato parametrico

-- cosa corrisponde alle regole per dedurre naturalmente il tutto a teoria

{-
            A     B
            ------- ∧ I
            A  ∧  B
-}


fst : ∀{A B : Set} → A ∧ B → A
fst (x , y) = x

{-
      A ∧ B
      ----- ∧₁ E
        A
-}

snd : ∀{A B : Set} → A ∧ B → B
snd (x , y) = y

{-
      A ∧ B
      ----- ∧₂ E
        B
-}


-- Disgiunzione

-- e : A ∨ B ( ∨ si scrive /or) se e è un' Evidenza di A oppure un' Evidenza di B con l'indicazione di quale delle due possibilità


-- deduzione naturale dell' or


{-

        A
     ------- ∨₁ I
     A  ∨  B
  
        B
     ------- ∨₂ I 
     A  ∨  B
   
-}


data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

infixr 2 _∨_

-- definiamo questi due perché:
-- ragionando in insiem di Evidenze, che cosè l' ∨?
-- E' l'insieme disgiunto delle dim. di A e di B 


{-
  se x : A allora inl x : A + B; se y : B allora inr y : A + B
  


-}


{- 
             [A]    [B]
              :      :
    A ∨ B     C      C                       A ∨ B    A → C   B → C
    ------------------ ∨E                    ---------------------- ∨E'
             C                                          C
 


      
-}

∨-elim : ∀{A B C : Set} → (A → C) → (B → C) → A ∨ B → C
-- nella logica costruttiva le freccie sono funzioni
∨-elim f g (inl x) = f x
∨-elim f g (inr x) = g x


-- dim. dell'∧ distribuisce sull'∨


-- Commutatività di ∧

∧-comm : ∀{A B : Set} → A ∧ B → B ∧ A
∧-comm (x , y) = y , x

-- chiedo ad Adgda come è fatta l'Evidenza di A -> ctrl +c ctrl + r


-- scritto in maniera puramente funzionale

-- ∧-comm = λ x → snd x , fst x

-- sono identiche le dim. 


-- dim. che l'∨ è indepotente

_⇔_ : Set → Set → Set   -- se e solo se /iff
A ⇔ B = (A → B) ∧ (B → A)

infixr 2 _⇔_

-- dato che A B C non sono in scope allora glieli passo come parametri impliciti

∧∨-dist : ∀{A B C : Set} → (A ∧ (B ∨ C)) ⇔ ((A ∧ B) ∨ (A ∧ C))
∧∨-dist {A} {B} {C}= only-if , if 
  where -- serve per def. helper function o funzioni locali, ci servono per smontare la dim. in più pezzi
   only-if : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)
   only-if (x , inl y) = inl (x , y)
   only-if (x , inr z) = inr (x , z)

   if : (A ∧ B) ∨ (A ∧ C) → A ∧ (B ∨ C)
   if (inl (x , y)) = x , inl y 
   if (inr (x , z)) = x , inr z


-- dim dell'es 2

∧-idem : ∀{A : Set} → A ∧ A ⇔ A 
∧-idem {A} = if , only-if
  where
   if : A ∧ A → A
   if (x , y) = x

   only-if : A → A ∧ A
   only-if x = (x , x)


-- dim dell es 2 ∨  

∨-idem : ∀{A : Set} -> A ⇔ A ∨ A
∨-idem {A} = if , only-if
  where
    if : A → A ∨ A
    if x = inl x

    only-if : A ∨ A → A
    only-if x = ∨-elim id id x


-- data T : Set where
--  <> : T

--∧-unit-l : ∀{A : Set} → A ⇔ T ∧ A 
--∧-unit-l {A} = if , only-if
--  where
--    if : A → T ∧ A
--   if x = (<> , _)

--    only-if : T ∧ A → A
--    only-if x = snd x

--∨-unit-l : ∀{A : Set} → A ⇔ ⊤ ∨ A
--∨-unit-l {A} = if , only-if
  --where
    --if : A → T ∨ A 
    --if x = inr x

    --only-if : T ∨ A → A
    --only-if x = {!!}


-- da finire

∧∨-dist2 : ∀{A B C : Set} → (A ∧ (B ∨ C)) ⇔ ((A ∧ B) ∨ (A ∧ C))
∧∨-dist2 {A} {B} {C} = if , if2
  where
      if : A ∧ (B ∨ C) → A ∧ B ∨ A ∧ C
      if (x , inl y) = inl (x , y)
      if (x , inr y) = inr (x , y) 

      if2 : A ∧ B ∨ A ∧ C → A ∧ (B ∨ C)
      if2 (inl (x , y)) = x , inl y
      if2 (inr (x , y)) = x , inr y


