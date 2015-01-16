\begin{code}
module PiWare.Samples.BoolTrioComb where

open import Data.Bool using () renaming (Bool to B)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import PiWare.Atom.Bool using (Atomic-B; False#; True#)
open import PiWare.Synthesizable Atomic-B
open import PiWare.Synthesizable.Bool
open import PiWare.Gates.BoolTrio using (BoolTrio; FalseConst#; TrueConst#; Not#; And#; Or#)
open import PiWare.Circuit.Core BoolTrio using (Gate)
open import PiWare.Plugs BoolTrio using (pFork×; pid; pALR; pARL; pFst; pSnd)
open import PiWare.Circuit BoolTrio using (ℂ; Combℂ; cc; Mkℂ; _⟫_; _||_; |+; _named_)
\end{code}


%<*fundamentals>
\begin{code}
⊥ℂ ⊤ℂ : Combℂ ⊤ B
⊥ℂ = cc (Mkℂ (Gate FalseConst#) named "falseGate")
⊤ℂ = cc (Mkℂ (Gate TrueConst#) named "trueGate")

¬ℂ : Combℂ B B
¬ℂ = cc (Mkℂ (Gate Not#) named "notGate")

∧ℂ ∨ℂ : Combℂ (B × B) B
∧ℂ = cc (Mkℂ (Gate And#) named "andGate")
∨ℂ = cc (Mkℂ (Gate Or#) named "orGate")
\end{code}
%</fundamentals>

%<*nand>
\begin{code}
¬∧ℂ : Combℂ (B × B) B
¬∧ℂ = cc (Combℂ.circ ∧ℂ ⟫ Combℂ.circ ¬ℂ named "nandGate")
\end{code}
%</nand>

%<*xor>
\begin{code}
⊻ℂ : Combℂ (B × B) B
⊻ℂ =  cc (pFork×
     ⟫ (Combℂ.circ ¬ℂ || pid ⟫ Combℂ.circ ∧ℂ) || (pid || Combℂ.circ ¬ℂ ⟫ Combℂ.circ ∧ℂ)
     ⟫ Combℂ.circ ∨ℂ)
\end{code}
%</xor>


-- a × b → c × s
-- %<*hadd>
-- \begin{code}
-- hadd : ℂ (B × B) (B × B)
-- hadd =   pFork×
--        ⟫ ∧ℂ || ⊻ℂ
--        named "hadd"
-- \end{code}
-- %</hadd>

-- (a × b) × cin → co × s
-- %<*fadd>
-- \begin{code}
-- fadd : ℂ ((B × B) × B) (B × B)
-- fadd =   hadd || pid
--        ⟫    pALR
--        ⟫ pid  || hadd
--        ⟫    pARL
--        ⟫ ∨ℂ   || pid
--        named "fadd"
-- \end{code}
-- %</fadd>


-- %<*mux2to1>
-- \begin{code}
-- mux2to1 : ℂ (B × (B × B)) B
-- mux2to1 =   pFork×
--           ⟫ (¬ℂ || pFst ⟫ ∧ℂ) || (pid || pSnd ⟫ ∧ℂ)
--           ⟫ ∨ℂ
--           named "mux2to1"
-- \end{code}
-- %</mux2to1>
