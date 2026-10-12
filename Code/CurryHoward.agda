module Code.CurryHoward where



-- Appofondimento su paradigma Curry-Howard :

{-
  tutti i lambda calcolo tipati utilizzano la proprietà di riduzione del soggetto

  Γ = x₁ : A₁ , ... , xₐ : Aₐ

  Γ ⊢ M : B

  Teorema della riduzione del soggetto : 
  (cosa dice? Γ = contesto, B = predicato ∨ Tipo, M = Soggetto)

  (supponiamo M con un certo tipo in un certo contesto)
  
  Γ ⊢ M : B ∧ M → β N ==> Γ ⊢  M : B 

  (dagli studi di Gentzen e Prawitz)

  (una dimostrazione è rindondante quando lo stesso connettivo viene prima introdotto e poi eliminato)

   Γ, x : A ⊢ M[x] : B                                             Γ ⊢ λ x : A . M[x] : A → B     Γ ⊢ N : A
  ---------------------- →I (freccia introduzione dei tipi)        ---------------------------------------- → E
  Γ ⊢ λ x :A . M[x] : A → B                                                Γ ⊢ (λ x : A . M[x]) N : B 


  Γ ⊢ M[N] : B (si riduce a questo e per il teorema di riduzione.. ha lo stesso tipo B e lo stesso contesto)

  Γ ⊢ M : A      Γ ⊢ N : B                                        Γ ⊢ P : A x B
  ----------------------- xI (introduzione del prodotto = And)    ------------- xE₁
  Γ ⊢ ⟨ M, N ⟩ : A x B                                            Γ ⊢ π₁ P : A
  ---------------------
  Γ : π₁ ⟨ M, N ⟩ : A
  
  π₁ ⟨ M, N ⟩ → M


-}
