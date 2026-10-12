module Code.Equalities where

open import Library.Bool
open import Library.Nat
open import Library.List
open import Library.Logic


-- l'uguaglianza è un datatype, è un oggetto di tipo Set


infix 4 _==_  -- infix = non è associativo ne a destra ne a sinistra

data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x
  


-- poniamo che l'uguaglianza venga fatta solo su un determinato tipo, ovvero non ha senso trovare l'uguaglianza di termini di tipo diverso 

-- tutto quello che cioò che uguagliamo è il fatto che da entrambe le parti abbiamo la stessa cosa a meno di riduzione
-- ovvero ridursi alla stessa forma normale


_ : true == true
_ = refl


_ : not true == false
_ = refl


_ : 5 + 7 == 12
_ = refl


-- proviamo ad esprimere il concetto di simmetria

symm : ∀{A : Set} {x y : A} → x == y → y == x
symm {_} {x} {.x} refl = refl


-- sono andato a dettagliare eq (ipotesi)
-- il punto al secondo parametro di x, denota il fatto che devono trattarsi dello stesso oggetto 

-- non me la cavo con refl percé il tipo dell'ipotesi è diverso dal goal che vogliamo trovare



trans : ∀{A : Set} {x y z : A} → x == y → y == z → x == z
trans refl refl = refl

-- questi refl generato dopo esser andato a dettagliare le due ipotesi sono due refl diversi

cong : ∀{A B : Set} (f : A → B) {x y : A} → x == y → f x == f y
cong f refl = refl


-- principio di sostituzione

-- P : predicato, cosè un predicato? Una funzione da A in Set
subst : ∀{A : Set} (P : A → Set) {x y : A} → x == y → P x → P y
subst P refl px = px



succ-injective : ∀{x y : ℕ} → succ x == succ y → x == y
succ-injective refl = refl



-- l' ipotesi eq : succ x == succ y implica che eq = refl : z == z
-- perché questo valga, bisogna che succ x e succ y, cui è istanziato z
-- siano uguali a meno di riduzione e unificazione, il che avviene ponendo x == y



-- def. la negazione

_!=_ : ∀{A : Set} → A → A → Set
x != y = ¬ (x == y)

zero-succ : ∀{x : ℕ} → zero != succ x
zero-succ ()



-- questa forma è (zero == succ x) → falso (ovvero la negazione)


-- mi viene 0 == succ x (tipo non abitato) perchè ?
-- perchè sono già due forme normali ma diverse e quindi non possono unificare
-- scopre che sono forme normali diverse e mi attacca il pattern ()


ne-ne : ∀{x y : ℕ} → succ x != succ y → x != y
ne-ne neq refl = neq refl


-- succ x != succ x = succ x == succ x → ⊥



::-injective : ∀{A : Set} {x y : A} {xs ys : List A} → x :: xs == y :: ys → x == y ∧ xs == ys
::-injective refl = refl , refl


-- un solo costruttore per ∧, infatti ho una coppia da inserire


















