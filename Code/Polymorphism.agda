module Code.Polymorphism where

open import Library.Bool
open import Library.Nat


-- lista tipica struttura dati parametrica (polimorfe) 


-- in C possono essere monomorfe

-- Il polimorfismo nasce con i linguaggi funzionali

id-Bool : Bool → Bool
id-Bool = λ(b : Bool) → b

-- posso cambiare il tipo da Bool ad altro

-- I tipi di agda sono tipi dipendenti

id : ∀(A : Set) → (x : A) → A
-- id x non posso farlo perché lo interpreta come tipo freccia
id A x = x


_ : ℕ
_ = id ℕ 47
-- non id 47 perché non specifico il tipo di 47
-- andrebbe bene anche con _ ovvero → = id _ 47

id' : ∀{A : Set} → (x : A) → A
id' x = x

_ : Bool
_ = id' true
