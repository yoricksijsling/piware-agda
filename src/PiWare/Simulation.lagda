\begin{code}
open import PiWare.Atom using (Atomic)
open import PiWare.Gates using (Gates)

module PiWare.Simulation {At : Atomic} (Gt : Gates At) where

open import Function using (_∘_)
open import Data.Nat using (ℕ)
open import Data.Stream using (Stream) renaming (map to mapₛ)

open import PiWare.Circuit Gt using (ℂ; comb; Mkℂ)
open import PiWare.Simulation.Core Gt using (⟦_⟧'; ⟦_⟧*')

open import PiWare.Synthesizable At using ()  -- only instances
open ⇓W⇑ ⦃ ... ⦄ using (⇓; ⇑)
\end{code}


%<*eval>
\AgdaTarget{⟦\_⟧}
\begin{code}
⟦_⟧ : ∀ {α i β j} (c : ℂ α β {i} {j}) {p : comb c} → (α → β)
⟦ Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ c' ⟧ {p} = ⇑ ∘ ⟦ c' ⟧' {p} ∘ ⇓
\end{code}
%</eval>

%<*eval-seq>
\AgdaTarget{⟦\_⟧*}
\begin{code}
⟦_⟧* : ∀ {α i β j} → ℂ α β {i} {j} → (Stream α → Stream β)
⟦ Mkℂ ⦃ sα ⦄ ⦃ sβ ⦄ c' ⟧* = mapₛ ⇑ ∘ ⟦ c' ⟧*' ∘ mapₛ ⇓
\end{code}
%</eval-seq>
