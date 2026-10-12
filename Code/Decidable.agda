module Code.Decidable where

open import Library.Nat
open import Library.Bool
open import Library.List
open import Library.Fun
open import Library.Equality
open import Library.Equality.Reasoning
open import Code.ConjDisj


-- particolarmente difficile da applicare in logica costruttiva

-- è una logica positiva perché si tratta sostanzialmente di dim. Evidenze



-- ¬  si scrive /neg


data ⊥ : Set where

-- la costante falso, il falso, non deve essere dimostrato

-- possiede una proprietà valida: se io fossi in grado di dim. il contrario allora posso fare il caso simmetrico


ex-falso : ∀{A : Set} → ⊥ → A
ex-falso = λ ()

-- questo pattern si genera in tutte le situazioni in cui il caso è impossibile

  -- il vero ⊤ si scrive /top

data ⊤ : Set where
  <> : ⊤


⊤-∧ : ∀{A : Set} → ⊤ ∧ A ⇔ A
⊤-∧ {A} = only-if , if
  where
    only-if : ⊤ ∧ A → A
    only-if x = snd x

    if : A → ⊤ ∧ A
    if x = <> , x

-- dimostrare che ⊥ ∨ A ⇔ A


-- l'uso che si fa della negazione sta nel trattare casi impossibili

¬_ : Set → Set 
¬ A = A → ⊥ -- ⊥ si scrive /bot

contradiction : ∀{A : Set} → ¬ A → A → ⊥
contradiction x y = x y

⊥-A : ∀{A : Set} → A ⇔ ⊥ ∨ A
⊥-A {A} = only-if , if
  where
    only-if : A → ⊥ ∨ A
    only-if x = inr x

    if : ⊥ ∨ A → A
    if (inr x) = x

-- il vero è una costante logica con un unica prova triviale



-- significa che se avessi una prova dell'Evidenza di A allora potrei dimostrarti l'assurdo

-- def. una prop. ⊥ ma dato che non def. nessun costruttore allora non devo dchiararlo come termine





-- devo arrivare a dim. ⊥, allora applico y ad x e ottengo ⊥

-- è come se piazzare l'op ¬ al fianco di A passato come parametro, per poi arrivare all'assurdo


{-
  corrisponde alla regola di ¬  E


  ¬ A     A
  ----------
       A 
  
-}



trivial : ⊥ → ⊥
trivial = λ z → z

contraposition : ∀{A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition x y z = y (x z)



double-negation : ∀{A : Set} → A → ¬ ¬ A
double-negation x y = y x


-- quando metto come argomento x perché penso che ci sia un argomento

-- in verità usando ¬ so di avere un altro argomento e quindi ne avrò sempre n + 1 con n : Numero di args. rispetto alle freccie



-- principio del terzo escluso : ¬ ¬ A ∨ A



-- decidable sarebbe Set₁ in quanto costruisce prop. a partire da esse

Decidable : Set → Set 
Decidable A = ¬ A ∨ A


-- affermiamo che l'uguaglianza tra booleani, naturali

pattern yes x = inr x
pattern no x = inl x

-- anche sulle liste

Bool-eq-decidable : ∀(x y : Bool) → Decidable (x == y)
Bool-eq-decidable true true = yes refl -- Decidable (true == true) = ¬ true == true → ⊥ ∨ true == true
Bool-eq-decidable true false = no λ () -- Decidable (true == false) = ¬ true == false ∨ true == false 
Bool-eq-decidable false true = no λ ()
Bool-eq-decidable false false = yes refl

-- tutte queste le concludo con ctrl c + ctrl a

Nat-eq-decidable : ∀(x y : ℕ) → Decidable (x == y)
Nat-eq-decidable zero zero = yes refl
Nat-eq-decidable zero (succ y) = no (λ ())
Nat-eq-decidable (succ x) zero = no (λ ())
Nat-eq-decidable (succ x) (succ y) with Nat-eq-decidable x y
... | yes p = yes (cong succ p)
... | no q  = no λ{ refl → q refl }



List-eq-decidable : ∀{A : Set} → (∀(x y : A) → Decidable (x == y)) → ∀(xs ys : List A) → Decidable (xs == ys)  
List-eq-decidable p [] [] = yes refl
List-eq-decidable p [] (x :: ys) = no (λ ())
List-eq-decidable p (x :: xs) [] = no (λ ())
List-eq-decidable p (x :: xs) (y :: ys) with p x y | List-eq-decidable p xs ys
... | yes u | yes v  = yes q 
  where
    q : x :: xs == y :: ys
    q = begin x :: xs ==⟨ cong (λ z → z :: xs) u ⟩
              y :: xs ==⟨ cong (λ z → y :: z) v ⟩
              y :: ys
        end
... | yes u | no  n  = no λ { refl → n refl}
... | no  n | _      = no λ{ refl → n refl}



-- voglio applicare due volte il with, nel secondo caso sulle code usando l' ip. induttiva

-- λ {} sto def. il λ secondo un certo tipo di pattern


-- metto yes + cong perché voglio dirgli che la disgiunzione l'ho dimostrata con la sua parte a sinistra della prop.


-- with : noi dobbiamo supporre che sia decibile che x == y 

-- ragioniamo induttivamente :
-- se sono due succ x succ y allora sono uguali se x y sono uguali ..
-- e tutti gli altri casi..


em-dm : (∀{A : Set} → ¬ A ∨ A ) → ∀{A : Set} → ¬ ¬ A → A
em-dm f {A} g with f {A}
... | inl p = ex-falso (g p)
... | inr q = q


-- ∀ x P(x) = π (x : A)(Px)
-- A → B    = π (x : A) B


de-morgan-3 : ∀{A B : Set} → ¬ (A ∨ B) → ¬ A ∧ ¬ B
de-morgan-3 hyp = (λ x → hyp (no x)) , (λ x → hyp (yes x))


nndec : ∀{A B : Set} → ¬ ¬ Decidable A
nndec p with de-morgan-3 p 
... | p,q = p (no (λ x → p (yes x)))


-- ¬ (¬ Decidable A) ⇔ ¬ (Decidable A) → ⊥ ⇔ ( ¬ (¬ A ∨ A)) → ⊥ 
-- p : ¬ ( ¬ A ∨ A)
-- de-morgan3 p : ¬ ¬ A ∧ ¬ A



dn-em : (∀{A : Set} → (¬ ¬ A → A)) → ∀{A : Set} → Decidable A
dn-em hyp = hyp nndec


∧-⊥-l : ∀{A : Set} → ⊥ ∧ A ⇔ ⊥
∧-⊥-l {A} = lemma1 , lemma2
  where
    lemma1 : ⊥ ∧ A → ⊥
    lemma1 x = fst x 

    lemma2 : ⊥ → ⊥ ∧ A
    lemma2 x = x , ex-falso x

-- altrimenti
-- ∧-⊥-l = fst, ex-falso

∨-⊤-l : ∀ {A : Set} → (⊤ ∨ A) ⇔ ⊤
∨-⊤-l = (λ x → <>) , inl 


succ-injective : ∀{x y : ℕ} -> succ x == succ y -> x == y
succ-injective refl = refl



_≠_ : ∀{A : Set} -> A -> A -> Set
x ≠ y = ¬ (x == y)

zero-succ : ∀{x : ℕ} -> zero ≠ succ x
zero-succ ()


::-injective : ∀{A : Set} {x y : A} {xs ys : List A} -> x :: xs == y :: ys -> x == y ∧ xs == ys
::-injective refl = refl , refl

cong23 : ∀{A B C : Set} (f : A -> B -> C) {x y : A} {u v : B} -> x == y -> u == v -> f x u == f y v
cong23 f refl refl = refl
