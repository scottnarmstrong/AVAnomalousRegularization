-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev

/-! The raw representative of the weak derivative of a given order and ordered word of a periodic
Sobolev field, as a total function. The carrier stores jets of order `≤ K` (`Fin (K+1)`); the
accessor returns the jet of order `m` when `m ≤ K` and `0` otherwise. Every use in the cycle
statements has `m ≤ K` structurally (the order of the field exceeds the derivative order that is
read), so the `0` branch is never reached; it exists only to keep the accessor total without a proof
argument. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- The raw jet of order `m` and word `w` of `W : TorusHk K E` (`0` if `m > K`). -/
def torusJetOrder {K : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (W : TorusHk K E) (m : ℕ)
    (w : DerivativeWord2 m) : Vec 2 → E :=
  fun x => if hm : m ≤ K then W.toFunction.jet ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩ x else 0

end AVRegularity
