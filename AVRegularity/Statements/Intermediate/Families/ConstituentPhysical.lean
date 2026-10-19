-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDimFlux
public import AVRegularity.Statements.Intermediate.Families.ChartInvJacobian
public import AVRegularity.Statements.Intermediate.Families.TransportedCoeff
public import AVRegularity.Statements.Intermediate.Families.ChartedFamily
public import AVRegularity.Statements.Intermediate.Families.ChartTransition
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The physical (Eulerian) coefficient assembled from the chart pieces of a family. In the
native chart of the piece `p`, with the actual context `actual p` selected, the dimensional sample
is `B_{p,γ,d,I}(t,y) = 𝔞_{p,c,γ,d,I}(t, y, y/e) = ν e^{d-2} a♭(t, y/E, y/e)`. The Eulerian array
of the piece is its exact inverse Piola/chain-rule transport (`transportedCoeff`)
along `Υ = Φ_p(t,·)⁻¹` (chart coordinate `y = Υ(x)`); the physical array is the sum over the
pieces with the prescribed time partition `weight`. A pure order `d` of a piece contributes to the
orders `2,…,d` of the physical array. The sum over constituents is taken here only to give the
PDE coefficient `A(t,x)`; the sampled envelope treats constituents separately. Fiber lists are
not the physical coefficient: a single physical coefficient or its diagonal jets do not
determine the independent fields. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The Eulerian order-`d` coefficient of one constituent `γ`: `A(t,x) g = ∑ᶠ_p weight_p(t)
(k ↦ ∑_A B̃^{p}_{γ,d,k,A}(t,x) C_γ g_A)` as an operator from the word array of `u`-values to the
flux array of `v`-values, where `B̃^p` is the transport (`transportedCoeff`) of the samples of
the piece `p` along `Υ_{p,t} = Φ_p(t,·)⁻¹`. -/
def constituentPhysical (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (actual : ∀ p, Ctx p)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (t : ℝ) (x : Vec 2) :
    (PiLp 2 (fun _ : DerivativeWord2 (d - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v)) :=
  ∑ᶠ p : P, F.weight p t •
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => h v)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun k : Fin 2 =>
        ∑ A : DerivativeWord2 (d - 1),
          (transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
              (F.identity v u γ).maxOrder
              (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I t
                (((F.piece p).material t).symm x) (e⁻¹ • ((F.piece p).material t).symm x))
              (d - 1) A x k) •
            (F.identity v u γ).map.comp (PiLp.proj 2 (fun _ : DerivativeWord2 (d - 1) => h u) A)))

end AVRegularity
