module Code.Naturals where

open import Library.Equality
open import Library.Equality.Reasoning

-- Reasoning = macro

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- 2 = succ (succ zero)
{-# BUILTIN NATURAL ℕ #-}

_ : 3 == succ (succ 1)
_ = refl

_+_ : ℕ → ℕ → ℕ
zero + y = y
succ x + y = succ ( x + y )


infixl 6 _+_

_*_ : ℕ → ℕ → ℕ
zero * y = zero
succ x * y = y + (x * y)

infixl 7 _*_

-- num : ℕ
-- num = 2 * (3 + 1)

-- Associatività di _+_

-- dim. funzionale, applico la ricorsione

-- teorema = +-assoc
+-assoc : ∀(x y z : ℕ) → x + (y + z) == (x + y) + z
-- noi vogliamo dimostrare che le forme normali, ambi i membri dell'uguale,
-- siano uguali, ovvero coincidano
+-assoc zero y z = refl -- goal mi dava giusta la soluzione

-- +-assoc zero y z = {refl}buco → mi da errore, perché non posso ridurre
-- le variabili ma solo i numeri stessi
-- i casi sono sempre due: zero e succ ..

-- se guardo la def. di somma, lo definita per induzione sul primo argomento
-- quindi mi conviene andare a prendere gli argomenti più a sinistra

-- faccio induzione sul parametro x → ctrl c + ctrl c 

-- +-assoc (succ x) y z = cong succ (+-assoc x y z)

-- ho usato la regola di congruenza = cong e l'ipotesi induttiva

-- tesi = succ (x + (y + z)) == succ (x + y + z)
-- lui omette le parentesi nella seconda uguaglianza, ovvero succ ((x + y)+ z )
-- devo lavorare sull'argomento del simbolo funzionale succ

--       x + (y + z)   ==   (x + y) + z
-- --------------------------------------- cong
--  succ (x + (y + z)) == succ (x + y + z)

-- cong ∀ (A B : Set) (f : A → B) (x y : A) → x == y → f x == f y

-- la regola cong si aspetta un ipotesi e mi sputa la tesi cerco

-- tesi = argomento della funzione = funzione ricorsiva = ipotesi induttiva

-- ho usato la regola di congruenza e l'ipotesi induttiva = chiamata ricorsiva della funzione appalicata ma senza il succ


-- dimostrazione tratta dalla deduzione naturale 
{-
+-assoc (succ x) y z = -- parto da questo termine e voglio arrivare a quello
-- di destra segnato denominato dal goal di agda
  
  -- questa tecnica usa la libreria Reasoning che utilizza formalismi e
  -- la proprietà di transitività  
 
  begin 
     (succ x) + (y + z) ==⟨⟩       -- per def. di +, mi ha portato fuori il succ
     succ (x + (y + z)) ==⟨ cong succ (+-assoc x y z)  ⟩ 
     -- nelle parentesi angolate vado a metterci la giustificazione del
     -- passaggio = ipotesi induttiva → cong succ ( +-assoc x y z  )
     succ (x + y + z)   ==⟨⟩
     (succ (x + y)) + z ==⟨⟩
     ((succ x ) + y) + z
  end 
     -- si scrive /< />
     -- giustificazione = ipotesi induttiva
-}

-- +-assoc : ∀(x y z : ℕ) → x + (y + z) == (x + y) + z

-- alt + w per copiare, ctrl + y per incollare



-- terzo modo di dim. il risultato 

+-assoc (succ x) y z rewrite (+-assoc x y z) = refl

-- la rewrite semplicemente passando l'opportuna ip. induttiva
-- si va a cercare la regola di cong = congruenza

-- Goal = Commutatività di + = tesi

-- Completare la dim.
+-unit-r : ∀(x : ℕ) → x == x + zero
+-unit-r zero     = refl
-- symm, funzione che sta in Equality 
+-unit-r (succ x) = cong succ (+-unit-r x)

-- mentre symm ( rewrite (..) ) -> mi gira x + zero = x così posso arrivare al goal

+-succ : ∀(x y : ℕ) → (succ x) + y == x + (succ y)
+-succ zero y     = refl
+-succ (succ x) y =  cong succ (+-succ x y)

-- potevo anche scrivere
-- +-succ (succ x) y rewrite (+-succ x y) = refl

+-comm : ∀(x y : ℕ) → x + y == y + x
-- devo fare induzione su x e poi una su y
+-comm zero y = +-unit-r y
-- y == y + zero : Goal
-- dato che fare induzione sia su x che y è difficile,
-- allora delego facendo un lemma +-unit-r
+-comm (succ x) y = 
  begin
    (succ x) + y ==⟨⟩ -- rendo esplicito questo passaggio anche se agda lo
                      -- aveva balzato
    -- Ma nonostante tutto non riesco a smuovermi rispetto al primo membro
    -- l'unica è rigirare x e y usato l'ipotesi induttiva, ovvero la comm
    succ (x + y) ==⟨ cong succ (+-comm x y) ⟩
    succ (y + x) ==⟨⟩
    -- passo successivo inutile, serve solo per capire che ho applicato il lemma di +-succ
    -- adesso posso usare il discorso che posso shiftare il succ su un altro
    -- argomento anzichè sul primo
    (succ y) + x ==⟨ +-succ y x ⟩
    y + succ x
  end


-- dimostrazione della commutatività rispetto allo 0 della moltiplicazione
*-zero-r : ∀(x : ℕ) → zero == x * zero
*-zero-r zero = refl
*-zero-r (succ x) = *-zero-r x
-- zero == succ x  * zero
-- tesi = *-zero-r =  zero == x * zero



*-succ : ∀(y x : ℕ) → y + (y * x) == y * succ x
*-succ zero x = refl
*-succ (succ y) x =
  begin
       succ(y + (x + (y * x))) ==⟨ cong succ (+-assoc y x (y * x))  ⟩
       -- quello che trovo è quell sotto
       succ((y + x) + (y * x)) ==⟨ cong (λ z → succ(z + (y * x))) (+-comm y x) ⟩
       -- utilizzo la λ per riscrivere un dato argomento dell'expr. (in questo caso la prima parentesi)
       succ((x + y) + (y * x)) ==⟨ cong succ (symm(+-assoc x y (y * x))) ⟩
       -- qua ho preso la simmetrica rispetto al lemma assoc def. precedentemente
       succ(x + (y + (y * x))) ==⟨ cong (λ z → succ(x + z)) (*-succ y x)  ⟩
       succ(x + (y * succ x))
  end
       




+-comma : ∀(x y : ℕ) → x * y == y * x
+-comma zero y  = *-zero-r y
+-comma (succ x) y =
  begin
     -- (y + (x * y)) == ⟨ cong (λ z → y + z ) ⟩
       (y + (x * y)) ==⟨ cong (λ z → y + z) (+-comma x y)⟩
       -- viene applicata la commutatività (x e y) in z (input della λ-expr) e poi viene applicata y + z 
       -- y + ( y * x ) == y * succ x
       (y + (y * x)) ==⟨ *-succ y x  ⟩
       (y * succ x) 
  end
       

*-succ2 : ∀(y x : ℕ) → y + (y * x) == y * succ x
*-succ2 zero y = refl
*-succ2 (succ x) y rewrite symm(*-succ2 (x) (y) ) -- ho preso la simmetrica dell'ipotesi induttiva, quind da destra a sinistra
                   | +-assoc (y) (x) (x * y) --  
                   | +-assoc (x) (y) (x * y) -- lo ripeto per togliere le parentesi
                   | +-comm (x) (y) = refl



+-comm2 : ∀(x y : ℕ) → x + y == y + x
+-comm2 zero y = +-unit-r y
+-comm2 (succ x) y rewrite +-comm2 x y
                   | +-succ y x = refl



*-succ3 : ∀(y x : ℕ) → y + (y * x) == y * succ x
*-succ3 zero y = refl
*-succ3 (succ x) y rewrite symm ( *-succ3 x y )
                   | +-assoc y x (x * y)
                   | +-assoc x y (x * y) -- questo sempre per togliere le parentesi
                   | +-comm y x = refl


-- succ (x + (y + x * y)) == succ (y + x * succ y)


-- succ (x + (y + x * y)) == succ (y + (x + x * y))
