module Code.Lambda where

open import Library.Nat

-- Tipi semplici
-- α è un tipo ( atomico, ad es. ℕ )
-- se A e B sono tipo allora A → B è un tipo

-- un tipo è un insieme di valori, il tipo → rappresenta l'insieme delle funzioni calcolabili e non


-- in Agda se A è un tipo semplice allora A : Set ≅ Set_0

-- la freccia associa a destra: A → B → C = A → (B → C)


-- x : A è un termine di tipo A
-- se M : B e x : A allora  λ(x : A) → M : A → B

-- se M : A → B e N : A allora M N : B
-- calcolo monomorfo(termine che ha un solo tipo), in contrasto con il polimorfismo che invece permette di avere un termine specializzato in più tipi



-- l'applica associa a sinistra M N L = (M N) L

-- agda implementa il lambda calcolo tipato con tipi indipendenti

{--

     M : A → B → C   N : A
   -------------------------
       M N : B → C          L:B
      ---------------------------
              M N L : C

    
      β) (λ(x : A) → M ) N = M [ x := N ] -- sostituisce tutte le occorrenze di x con in M -- Spesso considerata come riduzione 
    
         
--}



twice : (ℕ → ℕ) → ℕ → ℕ
-- non posso togliere le parentesi perché x si aspetta (ℕ → ℕ)
twice = λ( x : ℕ → ℕ ) → λ( y : ℕ) → x (x y)

{--

Γ = x : ℕ
  
  
_^_ : ℕ → ℕ → ℕ

_+_ : ℕ → ℕ → ℕ

2, 1 : ℕ

--}

f : ℕ → ℕ
f = λ(x : ℕ) → x ^ 2 + 1

f' : ℕ → ℕ
f' x = (x ^ 2) + 1

-- metto un '?' poi faccio ctl c + ctrl x → buco verde e poi chiedo il tipo ad agda con ctrl c + ctrl ',' e vedo se me lo da
-- altrimenti lo indovino e ctrl c + ctrl space

-- potrei mettere le parentesi in x ^ 2, non mi servono perché l'op. ^ precede la somma
-- riconosce che 2, il '+' e la costante 1 sono tutti tipi  ℕ 

-- g = λ x → (x ^ 2) + 1 


-- questo es da fare: (es 4 del libro)
-- λ (x : ℕ -> ℕ -> ℕ) (y : ℕ) -> x (x y)

-- le funzioni anonime(lambda expression) in un contesto non tipato non sono ricorsive


-- funzioni di più argomenti


g : ℕ → ℕ → ℕ -- ℕ x ℕ → ℕ 
-- g = λ ( x : ℕ ) → λ (y : ℕ) → x ^ 2 + 2 * x * y + 1

g = λ x y → x ^ 2 + 2 * x * y + 1

-- oppure g x y = ..


-- 1
--l :   
l  = λ (x :  (ℕ → ℕ) → ℕ) (z : ℕ → ℕ) → x z  

-- non tipa

-- 2


-- l = λ (x : ℕ → ℕ → ℕ) (y : ℕ ) → x y
-- tipa
-- es 3

  
-- l = λ (x :  ℕ -> ℕ → ℕ ) (y :  ℕ) ->  x ( x y )  

-- mi rimangono due ℕ e nel dom(x) non è concesso

-- es 4

-- l = λ (x : ℕ -> ℕ -> ℕ) (y : ℕ) -> x (x y)

-- non tipa

-- es 5

--l = λ (x : ℕ → ℕ → ℕ) (y : ℕ) → x y y

-- l = λ(x : ℕ ) (y : ℕ → ℕ) →  y x
