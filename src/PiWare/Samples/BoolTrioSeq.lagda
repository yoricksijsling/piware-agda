\begin{code}
module PiWare.Samples.BoolTrioSeq where

open import Data.Bool using () renaming (Bool to B)
open import Data.Unit using (⊤)
open import Data.Product using (_×_)

open import PiWare.Atom.Bool using (Atomic-B)
open import PiWare.Synthesizable Atomic-B
open import PiWare.Synthesizable.Bool
open import PiWare.Gates.BoolTrio using (BoolTrio)
open import PiWare.Plugs BoolTrio using (pid; pALR; pARL; pSwap; pFork×)
open import PiWare.Circuit BoolTrio using (ℂ; delayℂ; _⟫_; _||_; _named_)
open import PiWare.Samples.BoolTrioComb using (⊥ℂ; ¬ℂ; ∨ℂ; mux2to1)
\end{code}


%<*shift>
\begin{code}
shift shift^ : ℂ B B
shift^ = shift named "shift"
shift = delayℂ pSwap
\end{code}
%</shift>

%<*toggle>
\begin{code}
toggle toggle^ : ℂ ⊤ B
toggle^ = toggle named "toggle"
toggle = ⊥ℂ ⟫ delayℂ (∨ℂ ⟫ ¬ℂ ⟫ pFork×)
\end{code}
%</toggle>

-- input × load → out
%<*reg>
\begin{code}
reg reg^ : ℂ (B × B) B
reg^ = reg named "reg"
reg = delayℂ comb
    where rearrange = pSwap || pid  ⟫  pALR  ⟫  pid || pSwap
          comb      = rearrange  ⟫  mux2to1  ⟫  pFork×
\end{code}
%</reg>


-- (attempt at) generically-sized mux (to use the |+ constructor)
-- \begin{code}
-- mux : (n : ℕ) → let A = Vec B n  in  ℂ (A × Vec B (2 ^ n)) B {2 ^ n} {1}
-- mux zero = pSnd ⟫ pSingletonOut
-- mux (suc n) rewrite (proj₂ +-identity) (2 ^ n) =
--       pUncons || pid
--     ⟫        pALR
--     ⟫ pid ||  pFork× || pVecHalfPow
--     ⟫ pid ||     pIntertwine
--     ⟫ pid ||   mux n || mux n
--     ⟫              mux2to1
-- \end{code}
-- %</sample-mux>
