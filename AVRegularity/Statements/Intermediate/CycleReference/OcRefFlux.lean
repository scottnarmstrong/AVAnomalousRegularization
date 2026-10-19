-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.OcPulseMemory
public import AVRegularity.Statements.Intermediate.CycleReference.OcHStar
public import AVRegularity.Statements.Intermediate.CycleReference.OcPi
public import Mathlib.Topology.Instances.Matrix

/-! The reference flux `J = 𝐉_m^ν`, the averaged flux of display (1.16) of the paper. -/

@[expose] public section

namespace AVRegularity

/-- `J(t) = ν I + μ H_* ∑_{k odd} p_k(t) M_k(t) Π_k` (display (1.16) of the paper; all sums run
over odd slots). At each `t` at most one odd pulse is active, so the sum is finite. -/
noncomputable def ocRefFlux (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (ν t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
    (ocMu q Λ m ν * ocHStar α q Λ m ν) •
      ∑' k : {k : ℤ // Odd k},
        (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) • ocPi k

end AVRegularity
