-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.WordAdjoint
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The formal adjoint, on smooth periodic flux test fields of a Hilbert family, of the graded edge
flux `(F_E u)_v = ∑_{r=1}^H ∑_{u,d} C^{[r]}_{vu,d} ∇^{d-1} u_u` (`E = div F_E`, source degree `r`
along an original path of length `r`). The coefficient `C^{[r]}_{vu,d}(t,x)` maps the word array of
`u`-valued derivatives to the `ℝ²`-flux of the `v`-component;
`(F_E^* ψ)_u = ∑_{r,v,d} wordAdjoint ((C^{[r]}_{vu,d})^* ψ_v)`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `(F_E(t)^* ψ)_u (x) = ∑_{r=1}^H ∑_v ∑_{d=2}^D wordAdjoint (d-1)
(y ↦ adjoint (C^{[r]}_{vu,d}(t,y)) (ψ_v y)) (x)`. -/
def edgeFluxAdjoint {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] (D H : ℕ)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (t : ℝ) (ψ : ∀ v, Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) (u : ι) : Vec 2 → h u :=
  fun x => ∑ r ∈ Finset.Icc 1 H, ∑ v : ι, ∑ d : Finset.Icc 2 D,
    wordAdjoint (d.1 - 1) (fun y => ContinuousLinearMap.adjoint (CE r v u d t y) (ψ v y)) x

end AVRegularity
