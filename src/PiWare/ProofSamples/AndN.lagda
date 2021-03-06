\begin{code}
module PiWare.ProofSamples.AndN where

open import Function using (_∘_)
open import Data.Nat using (zero; suc; _*_)
open import Data.Bool using (true; _∧_)
open import Data.Vec using (replicate; [_]; _∷_)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import Algebra as A
import Data.Nat.Properties as NP
open A.CommutativeSemiring NP.commutativeSemiring using (*-identity)

open import PiWare.Gates.BoolTrio using (BoolTrio; spec-and)
open import PiWare.Samples.AndN using (andN'; andN'-comb; andN; andN-comb)
open import PiWare.Simulation.Core BoolTrio using (⟦_⟧')
open import PiWare.Simulation BoolTrio using (⟦_⟧)
\end{code}


%<*proof-andN-core-alltrue>
\AgdaTarget{proof-andN'-alltrue}
\begin{code}
proof-andN'-alltrue : ∀ n → ⟦ andN' n ⟧' {andN'-comb n} (replicate true) ≡ [ true ]
proof-andN'-alltrue zero    = refl
proof-andN'-alltrue (suc n) = cong (spec-and ∘ (_∷_ true)) (proof-andN'-alltrue n)
\end{code}
%</proof-andN-core-alltrue>

\begin{code}
\end{code}

%<*proof-andN-alltrue>
\AgdaTarget{proof-andN-alltrue}
\begin{code}
proof-andN-alltrue : ∀ n → ⟦ andN n ⟧ {andN-comb n} (replicate true) ≡ true
proof-andN-alltrue zero    = refl
proof-andN-alltrue (suc n) rewrite proof-andN-core-alltrue n = refl
\end{code}
%</proof-andN-alltrue>
