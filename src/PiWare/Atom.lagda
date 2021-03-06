\begin{code}
module PiWare.Atom where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec)

open import Relation.Binary.PropositionalEquality using (_≡_)
\end{code}


%<*Atomic>
\AgdaTarget{Atomic, Atom, n→atom, atom→n, inv-left, inv-right}
\begin{code}
record Atomic : Set₁ where
    field
        Atom     : Set
        |Atom|-1 : ℕ
        n→atom   : Fin (suc |Atom|-1) → Atom
        atom→n   : Atom → Fin (suc |Atom|-1)

        inv-left  : ∀ i → atom→n (n→atom i) ≡ i
        inv-right : ∀ a → n→atom (atom→n a) ≡ a

    |Atom| = suc |Atom|-1
    Atom#  = Fin |Atom|
    W = Vec Atom
\end{code}
%</Atomic>
