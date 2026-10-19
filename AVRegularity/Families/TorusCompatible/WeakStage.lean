-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
public import AVRegularity.Statements.Intermediate.CycleJoint.EdgeCoefficient
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.ChartIntegrandAlgebra
public import AVRegularity.Definitions.Entry.TerminalResidualClauses

@[expose] public section

section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity

/-! Integer translations and the chart-transport objects: derivatives of `ℤ²`-periodic maps are periodic, the inverse of an
integer-equivariant homeomorphism is integer-equivariant, the (inverse) Jacobian of an equivariant
map is periodic, and the order-lowering recursion `transitionT` and the transported array
`transportedCoeff` built from periodic fields are periodic. No differentiability is needed: the
translation identities of `fderiv` hold unconditionally. -/

namespace TorusCompatible

/-- The derivative of a `ℤ²`-periodic map is `ℤ²`-periodic. -/
theorem isZ2Periodic_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Vec 2 → F} (hf : IsZ2Periodic f) : IsZ2Periodic (fderiv ℝ f) := by
  intro n x
  have hfun : (fun y => f (y + latticeShift n)) = f := funext fun y => hf n y
  rw [← fderiv_comp_add_right (𝕜 := ℝ) (f := f) (latticeShift n), hfun]

/-- The derivative of an integer-equivariant map is `ℤ²`-periodic. -/
theorem isZ2Periodic_fderiv_of_equivariant {Υ : Vec 2 → Vec 2}
    (hΥ : ∀ (n : Fin 2 → ℤ) (y : Vec 2), Υ (y + latticeShift n) = Υ y + latticeShift n) :
    IsZ2Periodic (fderiv ℝ Υ) := by
  intro n x
  have hfun : (fun y => Υ (y + latticeShift n)) = fun y => Υ y + latticeShift n :=
    funext fun y => hΥ n y
  rw [← fderiv_comp_add_right (𝕜 := ℝ) (f := Υ) (latticeShift n), hfun,
    fderiv_add_const]

/-- The inverse of an integer-equivariant homeomorphism is integer-equivariant. -/
theorem symm_equivariant (Φ : Vec 2 ≃ₜ Vec 2)
    (hΦ : ∀ (n : Fin 2 → ℤ) (y : Vec 2), Φ (y + latticeShift n) = Φ y + latticeShift n)
    (n : Fin 2 → ℤ) (x : Vec 2) :
    Φ.symm (x + latticeShift n) = Φ.symm x + latticeShift n := by
  apply Φ.injective
  rw [hΦ, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

/-- The Jacobian of an integer-equivariant map is `ℤ²`-periodic. -/
theorem isZ2Periodic_chartJacobian {Υ : Vec 2 → Vec 2}
    (hΥ : ∀ (n : Fin 2 → ℤ) (y : Vec 2), Υ (y + latticeShift n) = Υ y + latticeShift n) :
    IsZ2Periodic (chartJacobian Υ) := by
  intro n x
  simp only [chartJacobian, isZ2Periodic_fderiv_of_equivariant hΥ n x]

/-- The inverse Jacobian of an integer-equivariant map is `ℤ²`-periodic. -/
theorem isZ2Periodic_chartInvJacobian {Υ : Vec 2 → Vec 2}
    (hΥ : ∀ (n : Fin 2 → ℤ) (y : Vec 2), Υ (y + latticeShift n) = Υ y + latticeShift n) :
    IsZ2Periodic (chartInvJacobian Υ) := by
  intro n x
  simp only [chartInvJacobian, isZ2Periodic_chartJacobian hΥ n x]

/-- The order-lowering recursion of a periodic inverse Jacobian is periodic (it uses only
derivatives, sums and products of periodic fields). -/
theorem isZ2Periodic_transitionT {K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hK : IsZ2Periodic K) :
    ∀ (I A : List (Fin 2)), IsZ2Periodic (transitionT K I A)
  | [], [] => fun _ _ => rfl
  | [], _ :: _ => fun _ _ => rfl
  | i :: I, A => by
      intro n y
      have hd := isZ2Periodic_fderiv (isZ2Periodic_transitionT hK I A) n y
      cases A with
      | nil => simp only [transitionT, hK n y, hd]
      | cons a A₀ =>
          simp only [transitionT, hK n y, hd, isZ2Periodic_transitionT hK I A₀ n y]

/-- The transported coefficient array of a periodic inverse Jacobian and a periodic
old-chart array is periodic. -/
theorem isZ2Periodic_transportedCoeff {K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hK : IsZ2Periodic K) (Dγ : ℕ) {B : Vec 2 → ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2}
    (hB : IsZ2Periodic B) (r : ℕ) (A : DerivativeWord2 r) :
    IsZ2Periodic (fun x => transportedCoeff K Dγ (B x) r A x) := by
  intro n x
  funext a₀
  simp only [transportedCoeff, hK n x, hB n x, isZ2Periodic_transitionT hK _ _ n x]

end TorusCompatible

/-! Torus compatibility gives periodic physical coefficients.

If the selected representatives of a charted family are torus compatible at the slow scale `E`
(`IsTorusCompatible`) and `e⁻¹ ∈ ℕ`, then for every piece the dimensional diagonal sample
`ν e^{d-2} a♭(t, Y/E, Y/e)` is `ℤ²`-periodic in `Y`, the inverse chart
`Υ_p = Φ_p(t,·)⁻¹` is integer-equivariant, its inverse Jacobian and the recursion `transitionT`
are periodic, hence so is the exact transported array. The time-only partition weights,
the constant maps, the locally finite piece sum and the finite constituent sum preserve the
equality, so every `constituentPhysical`, `physicalCoefficient` and `edgeCoefficient` is periodic
at every time. For the construction scales `e = ε_m`, `E = ε_{m-1}` the hypothesis `e⁻¹ ∈ ℕ`
always holds (`ocEpsilon_inv_natCast`). There is no estimate and no constant in the argument. -/

section
namespace TorusCompatible

/-- A natural multiple of an integer translation is an integer translation. -/
theorem natCast_smul_latticeShift (N : ℕ) (n : Fin 2 → ℤ) :
    (N : ℝ) • latticeShift n = latticeShift (fun i => (N : ℤ) * n i) := by
  funext i
  simp [latticeShift]

/-- The inverse of every construction wavelength is a natural number. -/
theorem ocEpsilon_inv_natCast (q : ℝ) (Λ m : ℕ) : ∃ N : ℕ, (ocEpsilon q Λ m)⁻¹ = N := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact ⟨1, by simp [ocEpsilon, hm]⟩
  · exact ⟨_, Construction.Stream.ocEpsilon_inv_eq_nat (q := q) (Λ := Λ) hm⟩

end TorusCompatible

namespace IsTorusCompatible

open TorusCompatible

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The inverse material chart of a torus-compatible family is integer-equivariant. -/
theorem symm_equivariant {F : ChartedFamily ι h D P Ctx} {actual : ∀ p, Ctx p} {E : ℝ}
    (hT : IsTorusCompatible F actual E) (p : P) (t : ℝ) (n : Fin 2 → ℤ) (x : Vec 2) :
    ((F.piece p).material t).symm (x + latticeShift n) =
      ((F.piece p).material t).symm x + latticeShift n :=
  TorusCompatible.symm_equivariant _ (hT.1 p t) n x

/-- The dimensional diagonal sample `ν e^{d-2} a♭(t, Y/E, Y/e)` of the selected representative is
`ℤ²`-periodic in `Y` when `e⁻¹ ∈ ℕ`. -/
theorem dimFlux_sample_periodic {F : ChartedFamily ι h D P Ctx} {actual : ∀ p, Ctx p} {E : ℝ}
    (hT : IsTorusCompatible F actual E) (ν e : ℝ) {N : ℕ} (he : e⁻¹ = N) (p : P) (v u : ι)
    (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) :
    IsZ2Periodic (fun Y => F.dimFlux ν e E p (actual p) v u γ d I t Y (e⁻¹ • Y)) := by
  intro n Y
  have hz : e⁻¹ • (Y + latticeShift n) = e⁻¹ • Y + latticeShift (fun i => (N : ℤ) * n i) := by
    rw [smul_add, he, natCast_smul_latticeShift]
  simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux, hz]
  rw [F.flux_periodic p (actual p) v u γ d I t (E⁻¹ • (Y + latticeShift n)) _ (e⁻¹ • Y)]
  have hY := hT.2 p t v u γ d I (e⁻¹ • Y) n Y
  simp only at hY
  rw [hY]

/-- Every constituent physical coefficient of a torus-compatible family is `ℤ²`-periodic at every
time when `e⁻¹ ∈ ℕ` (and the time-only piece assembly). -/
theorem constituentPhysical_periodic {F : ChartedFamily ι h D P Ctx} {actual : ∀ p, Ctx p}
    {E : ℝ} (hT : IsTorusCompatible F actual E) (ν e : ℝ) {N : ℕ} (he : e⁻¹ = N) (v u : ι)
    (γ : F.Γ v u) (d : ℕ) (t : ℝ) :
    IsZ2Periodic (constituentPhysical F ν e E actual v u γ d t) := by
  intro n x
  have hB : ∀ p : P, IsZ2Periodic (fun x : Vec 2 => fun d' (I : DerivativeWord2 (d' - 1)) =>
      F.dimFlux ν e E p (actual p) v u γ d' I t (((F.piece p).material t).symm x)
        (e⁻¹ • ((F.piece p).material t).symm x)) := by
    intro p m y
    funext d' I
    simp only [hT.symm_equivariant p t m y]
    exact hT.dimFlux_sample_periodic ν e he p v u γ d' I t m _
  have key : ∀ (p : P) (A : DerivativeWord2 (d - 1)),
      transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
          (F.identity v u γ).maxOrder
          (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I t
            (((F.piece p).material t).symm (x + latticeShift n))
            (e⁻¹ • ((F.piece p).material t).symm (x + latticeShift n)))
          (d - 1) A (x + latticeShift n) =
        transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
          (F.identity v u γ).maxOrder
          (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I t
            (((F.piece p).material t).symm x) (e⁻¹ • ((F.piece p).material t).symm x))
          (d - 1) A x := fun p A =>
    isZ2Periodic_transportedCoeff
      (isZ2Periodic_chartInvJacobian (hT.symm_equivariant p t)) _ (hB p) (d - 1) A n x
  simp only [constituentPhysical, key]

/-- Every physical coefficient of a torus-compatible family is `ℤ²`-periodic at every time when
`e⁻¹ ∈ ℕ`. -/
theorem physicalCoefficient_periodic {F : ChartedFamily ι h D P Ctx} {actual : ∀ p, Ctx p}
    {E : ℝ} (hT : IsTorusCompatible F actual E) (ν e : ℝ) {N : ℕ} (he : e⁻¹ = N) (v u : ι)
    (d : ℕ) (t : ℝ) :
    IsZ2Periodic (physicalCoefficient F ν e E actual v u d t) := by
  intro n x
  simp only [physicalCoefficient, hT.constituentPhysical_periodic ν e he v u _ d t n x]

/-- Every edge coefficient of a torus-compatible family is `ℤ²`-periodic at every time when
`e⁻¹ ∈ ℕ` (the coefficient identity of the integer-image transfer). -/
theorem edgeCoefficient_periodic {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*}
    {Ctx : P → Type*} {F : ChartedFamily ι h D P Ctx} {actual : ∀ p, Ctx p} {E : ℝ}
    (hT : IsTorusCompatible F actual E) (ν e : ℝ) (he : ∃ N : ℕ, e⁻¹ = N) (K : ι → ℕ)
    (v u : ι) (d : admissibleOrders K D v u) :
    ∀ t, IsZ2Periodic (edgeCoefficient F ν e E actual K v u d t) := by
  intro t
  obtain ⟨N, hN⟩ := he
  exact hT.physicalCoefficient_periodic ν e hN v u d.1 t

/-- The edge coefficients of the construction scales `e = ε_m`, `E = ε_{m-1}`: torus
compatibility at `ε_{m-1}` makes them `ℤ²`-periodic at every time (the integer-image transfer). -/
theorem edgeCoefficient_periodic_ocEpsilon {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*}
    {Ctx : P → Type*} {F : ChartedFamily ι h D P Ctx} {actual : ∀ p, Ctx p} {q : ℝ} {Λ m : ℕ}
    (hT : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1))) (ν : ℝ) (K : ι → ℕ) (v u : ι)
    (d : admissibleOrders K D v u) :
    ∀ t, IsZ2Periodic
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K v u d t) :=
  hT.edgeCoefficient_periodic ν _ (ocEpsilon_inv_natCast q Λ m) K v u d

end IsTorusCompatible
end

/-! The stages of the construction are torus compatible.

* `GenStage.material_equivariant`: the natural pieces `Φ_p(t,·) = X_{i-1}(t,·,s_p)` commute with
  integer translations (the renewal flows are lifts of torus maps,
  `CycleReference.streamFlow_lattice_equivariant`).
* `GenStage.isTorusCompatible_of_shiftInvariant`: a natural stage obeying the context-level law
  `IsShiftInvariant` is torus compatible at `E = ε_{i-1}`: at the native selected context (no
  children) an integer shift of the slow offset is an integer shift of the base label (the
  slow-offset clause), which the base-label clause absorbs.
* `IsStageInvariant.isTorusCompatible`, `IsGeneratedSeed.isTorusCompatible`: the stage invariant
  (which carries `IsNatural` and `IsShiftInvariant`) and hence every generated seed
  supply the premise `htorus` of `cycle_joint`/`cycle_comparison`. -/

section
namespace GenStage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The material maps of the natural pieces commute with integer translations. -/
theorem material_equivariant {G : GenStage D hr Dm b j₀} {M : ℕ} (hnat : G.IsNatural M)
    (p : OddSlot) (t : ℝ) (n : Fin 2 → ℤ) (Y : Vec 2) :
    (G.fam.piece p).material t (Y + latticeShift n) =
      (G.fam.piece p).material t Y + latticeShift n := by
  simp only [(hnat.1 p).2.2.2.2 t, OCData.flowOf]
  exact CycleReference.streamFlow_lattice_equivariant (D.hΦ _) t _ Y n

/-- A natural stage with the context-level torus law is torus compatible at its slow
scale `ε_{i-1}`. -/
theorem isTorusCompatible_of_shiftInvariant {G : GenStage D hr Dm b j₀} {M : ℕ}
    (hnat : G.IsNatural M) (hsh : G.IsShiftInvariant) :
    IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)) := by
  refine ⟨fun p t n Y => material_equivariant hnat p t n Y, ?_⟩
  intro p t v u γ d I z n Y
  show G.fam.flux p (G.actual p) v u γ d I t ((D.eps (G.level - 1))⁻¹ • (Y + latticeShift n)) z =
    G.fam.flux p (G.actual p) v u γ d I t ((D.eps (G.level - 1))⁻¹ • Y) z
  let c' : StageCtx D b j₀ G.level p :=
    ⟨(G.actual p).1.shiftBase n,
      (isAdmissibleChain_shiftBase D b j₀ G.level p.1 (G.actual p).1 n).2 (G.actual p).2⟩
  have h0 : (G.actual p).1.children = [] := by rw [hnat.2.2.1 p]; rfl
  rw [smul_add, hsh.2 p (G.actual p) c' n h0 rfl v u γ d I t, ← hsh.1 p (G.actual p) c' n rfl]

end GenStage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- A stage satisfying the stage invariant is torus compatible at `ε_{i-1}`: the premise `htorus`
of `cycle_joint` and `cycle_comparison` for the incoming stage of a passage. -/
theorem IsStageInvariant.isTorusCompatible {law : BirthLaw} {P : ProvParams}
    {seedK freshK : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ} {hφ₀ : MeasureTheory.Integrable φ₀} {M : ℕ}
    {k : InvConsts} {tA tB S θK : ℝ} {G : GenStage D hr Dm b j₀}
    (h : IsStageInvariant law P seedK freshK φ₀ hφ₀ M k tA tB S θK G) :
    IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)) :=
  GenStage.isTorusCompatible_of_shiftInvariant h.1 h.2.2.2.1

/-- A generated seed is torus compatible at `ε_{n-1}`. -/
theorem IsGeneratedSeed.isTorusCompatible {law : BirthLaw} {P : ProvParams}
    {seedK freshK : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ} {hφ₀ : MeasureTheory.Integrable φ₀} {M : ℕ}
    {kS : InvConsts} {seed : GenStage D hr Dm b j₀} {n : ℕ} {tS tf Ce τe : ℝ} {r₀ D₀ : ℕ}
    (h : IsGeneratedSeed law P seedK freshK φ₀ hφ₀ M kS seed n tS tf Ce τe r₀ D₀) :
    IsTorusCompatible seed.fam seed.actual (D.eps (n - 1)) := by
  rw [← h.1]
  exact h.2.2.2.2.2.2.2.1.isTorusCompatible
end

/-! The weak stage of terminal entry is torus compatible: `IsWeakStage` carries the stage invariant
at the weak constants, so the weak family supplies the premise `htorus` of
`cycle_joint`/`cycle_comparison` at its level `M = Gw.level` (the terminal preparation and the
physical error of `entry_terminal`). -/

section
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The weak stage is torus compatible at `ε_{M-1}`. -/
theorem IsWeakStage.isTorusCompatible {law : BirthLaw} {P : ProvParams} {φ₀ : Vec 2 → ℝ}
    {hφ₀ : MeasureTheory.Integrable φ₀} {M Mnat Jw dW DW : ℕ} {nW : ℕ+} {kW : InvConsts}
    {a T₀ σw CL Cχ χw : ℝ} {Gw : GenStage D ScalarH Dm b j₀} {aM : ℝ}
    (h : IsWeakStage law P φ₀ hφ₀ M Mnat Jw dW DW nW kW a T₀ σw CL Cχ χw Gw aM) :
    IsTorusCompatible Gw.fam Gw.actual (D.eps (M - 1)) := by
  rw [← h.2.2.1]
  exact h.2.2.2.2.2.2.2.2.2.isTorusCompatible
end

end AVRegularity
end
