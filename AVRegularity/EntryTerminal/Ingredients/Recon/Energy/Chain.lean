-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
import AVRegularity.CycleComparison.Coarse.Bound.FcNorm
public import AVRegularity.EntryTerminal.Ingredients.Recon.Coarse
public import AVRegularity.CycleComparison.Coarse.Fact.GradFluxIdent
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovTruncGDecomp
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.EntryTerminal.Ingredients.CoarseFamily.CoarseFamily
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.CycleComparison.Reconstruction.Continuity
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.FullLift.LiftCellSourceEffectiveAllDegrees
import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleReference.TorusStreamFluxEquation
import AVRegularity.Definitions.Finite.FiniteLiftBridge

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.FullLift
open scoped ENNReal
namespace AVRegularity.EntryTerminal.Ingredients.Recon.Energy

/-! # The covariance step of the energy of the coarse field

`energyCovStep`: if `W_i(t)` is the covariance image of `R_i(t)` (order `L`) for `t` in the
window, and `(R, R_w)` is a lift pair (`truncate R_w = R` a.e.), then the strong energy
`strongEnergyUpTo` of `W` at an order `m ≤ K'` is at most the covariance cost times the strong
energy of `(R, R_w)` (`covImage_strongEnergy_le` applied to the truncations of `W` and `R`, and
`strongEnergy_truncate_le`).

Special case: `W = 0`, `R = 0` gives `0 ≤ 0`. -/

section Jet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {μ : Measure (Vec 2)}

/-- The value part of `strongEnergyUpTo` at order `m ≤ K` is at most the full norm of the
truncation to order `K`. -/
theorem factorialNormSqUpTo_le_truncate {K L : ℕ} (hKL : K ≤ L) (ρ : ℝ) {m : ℕ} (hm : m ≤ K)
    (D : JetL2 μ L E) :
    factorialNormSqUpTo ρ m D ≤ factorialNormSq ρ (truncateJet (E := E) hKL D) := by
  classical
  let F : Fin (L + 1) → ℝ := fun j => factorialWeight ρ j.val *
    ∑ w : DerivativeWord2 j.val, ‖D ⟨j, w⟩‖ ^ 2
  let g : Fin (L + 1) → ℝ := fun j => if j.val ≤ m then F j else 0
  have hF : ∀ j, 0 ≤ F j := fun j => mul_nonneg (factorialWeight_nonneg _ _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hg : ∀ j, g j ≤ F j := fun j => by
    unfold g
    split_ifs
    · exact le_rfl
    · exact hF j
  change ∑ j, g j ≤ ∑ j' : Fin (K + 1), F (Fin.castLE (Nat.succ_le_succ hKL) j')
  have hsupp : ∀ j ∈ (Finset.univ : Finset (Fin (L + 1))), j ∉ (Finset.univ : Finset (Fin (K + 1))).image
      (Fin.castLE (Nat.succ_le_succ hKL)) → g j = 0 := by
    intro j _ hj
    unfold g
    split_ifs with h
    · exfalso
      exact hj (Finset.mem_image.2 ⟨⟨j.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    · rfl
  calc ∑ j, g j = ∑ j ∈ (Finset.univ : Finset (Fin (K + 1))).image
        (Fin.castLE (Nat.succ_le_succ hKL)), g j :=
        (Finset.sum_subset (Finset.subset_univ _) hsupp).symm
    _ = ∑ j' : Fin (K + 1), g (Fin.castLE (Nat.succ_le_succ hKL) j') :=
        Finset.sum_image (fun a _ b _ h => Fin.castLE_injective _ h)
    _ ≤ _ := Finset.sum_le_sum fun j' _ => hg _

end Jet

section Step

open AVRegularity.CycleComparison.Coarse

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

/-- Truncation preserves square integrability in time. -/
theorem memLp_truncate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L : ℕ} (hKL : K ≤ L)
    {ν : Measure ℝ} {f : ℝ → TorusHk L E} (hf : MemLp f 2 ν) :
    MemLp (fun t => truncateTorusHk hKL (f t)) 2 ν :=
  ((truncateTorusHk hKL).lipschitzWith.comp_memLp (map_zero _) hf)

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The strong energy up to order `m ≤ K'` of a field of order `K' + 1` is at most the strong
energy of the pair (truncation, field). -/
theorem energyUpTo_le_pair {K' m : ℕ} (hm : m ≤ K') (ρ ν a b : ℝ) (π : ι → ℝ)
    (Wf : ∀ i, ℝ → TorusHk (K' + 1) (h i)) :
    strongEnergyUpTo ρ ν π a b m Wf ≤
      strongEnergy ρ ν π a b (fun i t => truncateTorusHk (Nat.le_succ K') (Wf i t)) Wf := by
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul' le_rfl
  apply add_le_add
  · apply iSup_mono
    intro t
    apply iSup_mono
    intro _ht
    exact ENNReal.ofReal_le_ofReal
      (factorialNormSqUpTo_le_truncate (Nat.le_succ K') ρ hm (Wf i t).val)
  · apply mul_le_mul' le_rfl
    apply lintegral_mono
    intro t
    exact ENNReal.ofReal_le_ofReal (gradFactorialNormSqUpTo_le_gradFactorialNormSq ρ m _)

/-- The covariance image is unchanged by truncating both sides. -/
theorem isCovImage_truncate_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {k l k' l' : ℕ} (hk : k' ≤ k)
    (hl : l' ≤ l) (P : (Vec 2 → E) → Vec 2 → E) (Z : TorusHk k E) (W : TorusHk l E)
    (h : IsCovImage P Z W) : IsCovImage P (truncateTorusHk hk Z) (truncateTorusHk hl W) := by
  intro φ hφ hp
  have := h φ hφ hp
  change cellInner (tval (truncateTorusHk hl W)) φ = cellInner (tval (truncateTorusHk hk Z)) _
  rw [tval_truncateTorusHk, tval_truncateTorusHk]
  exact this

/-- **The covariance step.** -/
theorem energyCovStep {K K' p L m : ℕ} (hK : K = K' + 1) (hm : m ≤ K') (hL : K' + 2 * p ≤ L) {ρ : ℝ} (hρ : 0 < ρ)
    (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ν a b C : ℝ) (hC : 0 ≤ C)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Wf : ∀ i, ℝ → TorusHk K (h i)) (R : ∀ i, ℝ → TorusHk L (h i))
    (Rw : ∀ i, ℝ → TorusHk (L + 1) (h i))
    (hRw : ∀ i, MemLp (Rw i) 2 (volume.restrict (Set.Icc a b)))
    (hae : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncateTorusHk (Nat.le_succ L) (Rw i t) = R i t)
    (hval : ∀ i, ∀ t ∈ Set.Icc a b,
      IsCovImage (AVRegularity.covPolyP (Hc t) p) (R i t) (Wf i t))
    (hcost : ∀ t ∈ Set.Icc a b, covPolyConst (fbCovConst ρ (Hc t) (K' + 2 * p)) p ≤ C) :
    strongEnergyUpTo ρ ν π a b m Wf ≤
      ENNReal.ofReal C * strongEnergy ρ ν π a b R Rw := by
  subst hK
  have hv : K' + 2 * p + 1 ≤ L + 1 := Nat.succ_le_succ hL
  have hvMem : ∀ i, MemLp (fun t => truncateTorusHk hv (Rw i t)) 2
      (volume.restrict (Set.Icc a b)) := fun i => memLp_truncate hv (hRw i)
  have hvalue : ∀ i, ∀ t ∈ Set.Icc a b, IsCovImage (AVRegularity.covPolyP (Hc t) p)
      (truncateTorusHk hL (R i t)) (truncateTorusHk (Nat.le_succ K') (Wf i t)) :=
    fun i t ht => isCovImage_truncate_pair hL (Nat.le_succ K') _ _ _ (hval i t ht)
  have hgrad : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      IsCovImage (AVRegularity.covPolyP (Hc t) p) (truncateTorusHk hv (Rw i t)) (Wf i t) := by
    intro i
    filter_upwards [hae i, ae_restrict_mem measurableSet_Icc] with t htr ht φ hφ hp
    have := hval i t ht φ hφ hp
    change cellInner (tval (Wf i t)) φ = cellInner (tval (truncateTorusHk hv (Rw i t))) _
    have e : tval (truncateTorusHk hv (Rw i t)) = tval (R i t) := by
      rw [tval_truncateTorusHk, ← htr, tval_truncateTorusHk]
    rw [e]
    exact this
  have h2 : strongEnergy ρ ν π a b (fun i t => truncateTorusHk (Nat.le_succ K') (Wf i t)) Wf ≤
      ENNReal.ofReal C * strongEnergy ρ ν π a b (fun i t => truncateTorusHk hL (R i t))
        (fun i t => truncateTorusHk hv (Rw i t)) :=
    covImage_strongEnergy_le (K := K') (p := p) hρ Hc ν a b C hC π hπ
      (fun i t => truncateTorusHk (Nat.le_succ K') (Wf i t)) Wf
      (fun i t => truncateTorusHk hL (R i t)) (fun i t => truncateTorusHk hv (Rw i t))
      hvMem hvalue hgrad hcost
  have h3 : strongEnergy ρ ν π a b (fun i t => truncateTorusHk hL (R i t))
        (fun i t => truncateTorusHk hv (Rw i t)) ≤ strongEnergy ρ ν π a b R Rw :=
    strongEnergy_truncate_le hL ρ ν π a b R Rw
  exact (energyUpTo_le_pair hm ρ ν a b π Wf).trans (h2.trans (mul_le_mul' le_rfl h3))

end Step

end AVRegularity.EntryTerminal.Ingredients.Recon.Energy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
open scoped ENNReal
namespace AVRegularity.EntryTerminal.Ingredients.Recon.Energy

/-! # The clause statements for the energy of the coarse field

`termReconEnergy` is assembled from three statements at a context.

* `EnergyLargeStatement`: for a large level, the covariance primitive of the terminal menu is at
  most `4ρ²` on the window (and continuous), and the diagonal entries of the readout from the
  retained family to the weak family are at most one (the terminal law `lawT` has `c_H = cHP`
  arbitrary, so the entries are small only for large `M`).
* `EnergyChainStatement`: at such a context `W = P_pZ` is continuous on the window and its
  `strongEnergyUpTo` is at most `κ_cov √(fiber)` times the strong energy of the retained solution
  (`covImage_strongEnergy_le`, `actual_readoutEnergy_le`).
* `EnergySolutionStatement`: the strong energy of the retained solution is at most
  `√2 max(C_P,0) ‖f‖₂` (`native_reg_solution_strongEnergy_of_initial_norm`, `c.prepB`).

Special case: `f = 0` gives `Z₀ = 0`, the solution vanishes and `W = 0`. -/

section
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
    Ce cker j₀ M)

/-- The readout of the retained solution to the weak components. -/
abbrev eZr : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (A.Khat Kout) (ScalarH v.1.root) :=
  fun v t => succReadout M (c.D.eps (M - 1)) A.η₀ (A.Khat Kout) (fun v' => c.Z v' t) v

/-- The readout of the order-`K̂ + 1` lift of the retained solution. -/
abbrev eZrw : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk (A.Khat Kout + 1) (ScalarH v.1.root) :=
  fun v t => succReadout M (c.D.eps (M - 1)) A.η₀ (A.Khat Kout + 1) (fun v' => c.Zw v' t) v

/-- **Largeness of the level at a context**: the covariance primitive at the anchor is at most
`4ρ²` on the window and continuous in time, and the diagonal entries of the readout are at most
one. -/
def EnergyLargeAt : Prop :=
  (∀ t ∈ Set.Icc c.tp (c.tp + rTobs c),
      AVRegularity.CycleComparison.Coarse.covBound (termCovPrimitive c.D M c.tp t) ≤
        4 * rRho c ^ 2) ∧
    ContinuousOn (fun t => termCovPrimitive c.D M c.tp t) (Set.Icc c.tp (c.tp + rTobs c)) ∧
    ∀ (v : CompIn c.Gw.comps) (w : CompIn (c.Gt'.retained M 1 A.RT).comps),
      compParent M w.1 = v.1 →
        (Real.sqrt (c.Gw.mass c.lawW v))⁻¹ /
            (Real.sqrt ((c.Gt'.retained M 1 A.RT).mass c.lawT w))⁻¹ *
          c.D.eps (M - 1) ^ (A.η₀ * ((compWord M w.1).length : ℝ)) ≤ 1

/-- **The chain at a context.** At a large level, `W = P_pZ` is continuous on the window and its
strong energy at the density order `m'` is at most `κ_cov √(fiber)` times the strong energy of
the retained solution `(Z, Z_w)`. -/
def EnergyChainAt (kc ℓ : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) : Prop :=
  rpord A ℓ ≤ kc + (A.NT + A.Dt) → EnergyLargeAt c →
    (∀ v, ContinuousOn (reconW c kc hW v) (Set.Icc c.tp (c.tp + rTobs c))) ∧
    strongEnergyUpTo (rRho c) (c.D.κ (M - 1)) (c.Gw.mass c.lawW) c.tp (c.tp + rTobs c)
        (rpord A ℓ) (reconW c kc hW) ≤
      ENNReal.ofReal (AVRegularity.CycleComparison.Coarse.covPolyConst
          (4 * ((A.Khat Kout : ℕ) : ℝ) ^ 2) A.pT *
        Real.sqrt ((wordsUpTo A.alph (A.RT + 1)).card + 1)) *
        strongEnergy (rRho c) (c.D.κ (M - 1)) ((c.Gt'.retained M 1 A.RT).mass c.lawT)
          c.tp (c.tp + rTobs c) c.Z c.Zw

/-- The strong energy of the retained solution at a context. -/
def EnergySolutionAt : Prop :=
  strongEnergy (rRho c) (c.D.κ (M - 1)) ((c.Gt'.retained M 1 A.RT).mass c.lawT)
      c.tp (c.tp + rTobs c) c.Z c.Zw ≤
    ENNReal.ofReal (Real.sqrt 2 * max CP 0 * c.normF)

/-- **Open (largeness).** For every `cHP` there is a level `M₀` from which the covariance
primitive is small and the readout entries are at most one (`bandChain_covariance_estimates`,
`ε_{M-1} → 0`, and the product of the birth masses of the terminal law). -/
def EnergyLargeStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
    ∀ cHP' : ℝ, ∃ M₀ : ℕ,
      ∀ {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+} {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts}
        {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts} {cP CP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ},
        M₀ ≤ M →
        ∀ (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP' Cw
          Ce cker j₀ M) (_ : TermResAux c), EnergyLargeAt c

/-- **Open (chain).** -/
def EnergyChainStatement : Prop :=
  ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
    {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
    {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (_ : TermResAux c) (kc ℓ : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT), 128 ≤ A.Λ → 1 ≤ M →
    EnergyChainAt c kc ℓ hW

/-- **Open (solution energy).** -/
def EnergySolutionStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ →
    ∀ {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+} {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts}
      {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts} {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ}
      {j₀ M : ℕ}, 2 ≤ M →
      ∀ (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
        Ce cker j₀ M) (_ : TermResAux c), EnergySolutionAt c
end

/-! # The assembly of `termReconEnergy` from the three energy statements

The constant is `C_s = κ_cov √(fiber) · √2 · max(C_P, 0)` with `κ_cov = ∑_{l ≤ p_T} (4K̂²)^l / l!`;
it is chosen after `K_out`, `C_P`, `c_HP`. -/

/-- **The energy bound from the three energy statements.** -/
theorem termReconEnergy_of_statements (hL : EnergyLargeStatement) (hC : EnergyChainStatement)
    (hS : EnergySolutionStatement) : TermReconEnergyStatement := by
  intro ℓ X
  obtain ⟨ΛL, hΛL, hL⟩ := hL X
  obtain ⟨ΛS, hΛS, hS⟩ := hS X
  refine ⟨max ΛL ΛS, le_trans hΛL (le_max_left _ _), fun A hΛ hV => ⟨rpord A ℓ, fun kc hkc =>
    ⟨0, 0, 0, fun sXT sZT _ _ Kout _ => ⟨0, fun Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _
      cK CK CL Cχ Cread Cid kW _ _ _ cP CP cHP Cw Ce cker hcP => ?_⟩⟩⟩⟩
  obtain ⟨M₁, hM₁⟩ := hL A (le_trans (le_max_left _ _) hΛ) hV cHP
  have hK0 : 0 ≤ AVRegularity.CycleComparison.Coarse.covPolyConst
      (4 * ((A.Khat Kout : ℕ) : ℝ) ^ 2) A.pT * Real.sqrt ((wordsUpTo A.alph (A.RT + 1)).card + 1) :=
    mul_nonneg (Finset.sum_nonneg fun l _ => div_nonneg (pow_nonneg (by positivity) l)
      (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
  refine ⟨⟨(AVRegularity.CycleComparison.Coarse.covPolyConst
      (4 * ((A.Khat Kout : ℕ) : ℝ) ^ 2) A.pT * Real.sqrt ((wordsUpTo A.alph (A.RT + 1)).card + 1)) *
      (Real.sqrt 2 * max CP 0), mul_nonneg hK0 (mul_nonneg (Real.sqrt_nonneg _)
        (le_max_right _ _))⟩, 1, 1, le_rfl, one_pos, fun j₀ _ => ⟨max M₁ 2, fun M hM c x hW => ?_⟩⟩
  have hM1 : M₁ ≤ M := le_trans (le_max_left _ _) hM
  have hM2 : 2 ≤ M := le_trans (le_max_right _ _) hM
  have hΛ' : 128 ≤ A.Λ := le_trans (le_trans hΛL (le_max_left _ _)) hΛ
  have hlarge := hM₁ hM1 c x
  have hch := hC c x kc ℓ hW hΛ' (by omega) (by omega) hlarge
  have hsol := hS A (le_trans (le_max_right _ _) hΛ) hM2 c x
  refine ⟨hch.1, hch.2.trans ?_⟩
  calc _ ≤ _ := mul_le_mul_right hsol _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hK0]
      congr 1
      ring

end AVRegularity.EntryTerminal.Ingredients.Recon.Energy
end
end
end

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity Filter Topology
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.EntryTerminal.Ingredients.Recon.Energy

/-! # Largeness of the level

`energyLarge : EnergyLargeStatement`. For a large level the covariance primitive of the terminal
menu is at most `4ρ²` on the window (`bandChain_covariance_estimates`, as in `covTruncSize`), it is
continuous in time, and the diagonal entries of the readout from the retained family to the weak
family are at most one: a retained component is `succComp M v t` with `v` a weak component, its
mass under the terminal law is `(c_HP/|𝔚|) ε_{M-1}^{η₀/2}` times that of `v`, and this price is at
most one once `c_HP ε_{M-1}^{η₀/2} ≤ 1`.

Special case: an old component (`t = []`) has entry `ε^0 = 1`. -/

/-- **The readout entry from a weak component.** A component whose parent has no births has a
readout entry at most one when the birth price is at most one. -/
theorem energyEntry_le_one {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (law lawW : BirthLaw)
    (hroot : law.rootMass = lawW.rootMass) (m : ℕ) (hprice : law.cH / (law.wordCount : ℝ) *
      ocEpsilon q Λ (m - 1) ^ law.etaB ≤ 1) (v w : Comp) (hv : v.births = [])
    (hw : compParent m w = v) {η : ℝ} (hη : 0 ≤ η) :
    (Real.sqrt (compMass q Λ lawW v))⁻¹ / (Real.sqrt (compMass q Λ law w))⁻¹ *
      ocEpsilon q Λ (m - 1) ^ (η * (compWord m w).length) ≤ 1 := by
  have hmv : compMass q Λ lawW v = compMass q Λ law v := by
    unfold compMass
    rw [hv, ← hroot]
    simp
  have hcoef := readout_coefficient_le_one hq hΛ hη m w
  have hσ := (Construction.Preservation.Buffer.birth_compMass_pos hq hΛ law w).le
  have hπ := Construction.Preservation.Buffer.birth_compMass_pos hq hΛ law v
  have he : (Real.sqrt (compMass q Λ lawW v))⁻¹ / (Real.sqrt (compMass q Λ law w))⁻¹ =
      Real.sqrt (compMass q Λ law w / compMass q Λ lawW v) := by
    simpa only [one_mul, div_self (by norm_num : (1 : ℝ) ≠ 0), mul_one] using
      inverse_mass_diagonal_ratio hσ 1 1
  rw [he]
  refine (mul_le_mul ?_ hcoef (Real.rpow_nonneg (Scales.epsilon_basic (m := m - 1) hq hΛ).1.le _)
    zero_le_one).trans_eq (one_mul 1)
  refine Real.sqrt_le_one.mpr ?_
  rw [hmv, div_le_one hπ]
  have hwv : w = succComp m v (compWord m w) := by
    have := succComp_parent_word m w
    rw [hw] at this
    exact this.symm
  by_cases ht : compWord m w = []
  · rw [hwv, ht]
    simp [succComp]
  · rw [hwv, succComp_mass law v ht]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hprice hπ.le

/-- **Largeness of the level.** -/
theorem energyLarge : EnergyLargeStatement := by
  intro X
  obtain ⟨Ccov, hC1, Λ₁, hΛ₁, hest⟩ := CycleReference.bandChain_covariance_estimates X.hα₀ X.hα₁
    X.hs₀ X.hs₁ X.hq X.hζ
  refine ⟨Λ₁, hΛ₁, fun A hΛ hV cHP' => ?_⟩
  have hΛ128 : 128 ≤ A.Λ := hΛ₁.trans hΛ
  have hδ : 0 < ocDelta X.α X.q := ocDelta_pos_of_admissible X.hα₀ X.hq
  have hη : 0 < A.η₀ := hV.2.2.2.1.2.2.2.2.2.2.2.1
  have ht := CycleReference.epsilon_parent_tendsto_zero X.hq.1 hΛ128
  have hev1 : ∀ᶠ M : ℕ in atTop, Ccov * ocEpsilon X.q A.Λ (M - 1) ^ ocDelta X.α X.q ≤ 1 := by
    have h1 := ht.rpow_const (p := ocDelta X.α X.q) (Or.inr hδ.le)
    have h2 := (tendsto_const_nhds (x := Ccov)).mul h1
    rw [Real.zero_rpow hδ.ne', mul_zero] at h2
    exact h2.eventually (eventually_le_nhds one_pos)
  have hev2 : ∀ᶠ M : ℕ in atTop, cHP' * ocEpsilon X.q A.Λ (M - 1) ^ (A.η₀ / 2) ≤ 1 := by
    have h1 := ht.rpow_const (p := A.η₀ / 2) (Or.inr (by positivity))
    have h2 := (tendsto_const_nhds (x := cHP')).mul h1
    rw [Real.zero_rpow (by positivity), mul_zero] at h2
    exact h2.eventually (eventually_le_nhds one_pos)
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.1 (hev1.and hev2)
  refine ⟨max M₁ 2, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP Cw Ce cker j₀ M hM c x
  obtain ⟨hDα, hDq, hDΛ, hDζ, -, hband, -⟩ := c.data
  have hM2 : 2 ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨hsmall1, hsmall2⟩ := hM₁ M (le_trans (le_max_left _ _) hM)
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ128
  have hq1 : 1 < c.D.q := hDq ▸ X.hq.1
  have hΛD : 128 ≤ c.D.Λ := hDΛ ▸ hΛ128
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos hΛ1 X.hζ hband (Nat.sub_le M 1)
  have hνM : 0 < c.D.κ M := CycleReference.bandChain_pos hΛ1 X.hζ hband le_rfl
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (α := c.D.α) (q := c.D.q)
    (hDΛ ▸ hΛ1)
  have hε : ∀ r : ℝ, c.D.eps (M - 1) ^ r = ocEpsilon X.q A.Λ (M - 1) ^ r := by
    intro r
    simp only [OCData.eps]
    rw [hDq, hDΛ]
  refine ⟨?_, ?_, ?_⟩
  · intro t _
    have e1 : termCovPrimitive c.D M c.tp t =
        ocCovariance X.α X.q A.Λ X.ζ M (c.D.κ M) (c.D.κ (M - 1)) c.tp t := by
      simp only [termCovPrimitive]
      rw [hDα, hDq, hDΛ, hDζ]
    have e3 : rRho c = ocRh X.α X.q A.Λ M (c.D.κ (M - 1)) := by
      simp only [rRho, ocRh]
      rw [hDα, hDq, hDΛ]
    have hρpos : 0 < rRho c := Real.sqrt_pos.2 (mul_pos hν hh)
    have hpos : 0 < ocRh X.α X.q A.Λ M (c.D.κ (M - 1)) ^ 2 := e3 ▸ pow_pos hρpos 2
    have hentry : ∀ i j, |termCovPrimitive c.D M c.tp t i j| ≤ rRho c ^ 2 := by
      intro i j
      have h := (hest A.Λ hΛ M (by omega) c.D.κ hband M hM2 le_rfl c.tp t i j).2.2.2
      have h2 := (div_le_iff₀ hpos).1 h
      rw [e1, e3]
      refine h2.trans ?_
      rw [e3] at *
      calc _ ≤ 1 * ocRh X.α X.q A.Λ M (c.D.κ (M - 1)) ^ 2 :=
            mul_le_mul_of_nonneg_right hsmall1 (sq_nonneg _)
        _ = _ := one_mul _
    simp only [AVRegularity.CycleComparison.Coarse.covBound, Fin.sum_univ_two]
    have := hentry 0 0
    have := hentry 0 1
    have := hentry 1 0
    have := hentry 1 1
    linarith
  · have hc : Continuous (fun t => termCovPrimitive c.D M c.tp t) := by
      have := covTrunc_primitive_continuous (α := c.D.α) (q := c.D.q) (m := M) (Λ := c.D.Λ)
        (ζ := c.D.ζ) (hDΛ ▸ hΛ1) (hDζ ▸ X.hζ) (ν := c.D.κ M) (B := c.D.κ (M - 1)) hνM c.tp
      exact this
    exact hc.continuousOn
  · intro v w hw
    have hroots : ∀ v : CompIn c.Gw.comps, v.1.births = [] := c.weak.2.2.2.2.1
    obtain ⟨hroot, -, hcH, -, hwc, hηB, -⟩ := c.law
    have hwc1 : (1 : ℝ) ≤ (c.lawT.wordCount : ℝ) := by
      have : 1 ≤ c.lawT.wordCount := by rw [hwc]; exact le_max_left _ _
      exact_mod_cast this
    have hcpos := c.lawT.cH_pos
    have hprice : c.lawT.cH / (c.lawT.wordCount : ℝ) * ocEpsilon c.D.q c.D.Λ (M - 1) ^ c.lawT.etaB ≤ 1 := by
      have hp : c.lawT.cH * ocEpsilon c.D.q c.D.Λ (M - 1) ^ c.lawT.etaB ≤ 1 := by
        have e1 : ocEpsilon c.D.q c.D.Λ (M - 1) ^ c.lawT.etaB =
            ocEpsilon X.q A.Λ (M - 1) ^ (A.η₀ / 2) := by
          rw [hηB]
          exact hε _
        rw [e1, hcH]
        exact hsmall2
      have hpow : 0 ≤ ocEpsilon c.D.q c.D.Λ (M - 1) ^ c.lawT.etaB :=
        Real.rpow_nonneg (Scales.epsilon_basic hq1 hΛD).1.le _
      calc _ ≤ c.lawT.cH * ocEpsilon c.D.q c.D.Λ (M - 1) ^ c.lawT.etaB := by
            gcongr
            exact div_le_self hcpos.le hwc1
        _ ≤ 1 := hp
    exact energyEntry_le_one hq1 hΛD c.lawT c.lawW hroot M hprice v.1 w.1 (hroots v) hw
      (le_of_lt hη)

end AVRegularity.EntryTerminal.Ingredients.Recon.Energy
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.EntryTerminal.Ingredients
open AVRegularity.Construction.Residual.Presentation
open scoped ENNReal
namespace AVRegularity.EntryTerminal.Ingredients.Recon.Energy

/-! # The strong energy of the retained solution at a context

`energySolution : EnergySolutionStatement`. The retained solution `(Z, Z_w, Z_k)` of the context
is a regular solution from the trace `Z₀` of `P_term V(a_M)`; its strong energy at the radius
`ρ = √(κ_{M-1} τ''_M)` is at most `√2` times the weighted norm of `Z₀`
(`native_reg_solution_strongEnergy_of_initial_norm`, with the drift data of `coarse_drift_small`),
and that norm is at most the weighted norm of the trace `P_term V(a_M)` (`terminalTrace_weightedNorm_le`),
which `c.prepB` bounds by `C_P ‖f‖₂`.

Special case: `f = 0` gives the bound `0`. -/

/-- **The strong energy of the retained solution.** -/
theorem energySolution : EnergySolutionStatement := by
  intro X
  obtain ⟨ΛD, B₀, _, hΛD, hB₀, _, hdr⟩ := CycleComparison.Assembly.coarse_drift_small X.α X.s
    X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq X.ζ X.hζ
  refine ⟨ΛD, hΛD, fun A hΛ Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP
    Cw Ce cker j₀ M hM c x => ?_⟩
  by_cases htime : c.tp ≤ c.a + A.T₀
  swap
  · have hemp : Set.Icc c.tp (c.tp + rTobs c) = ∅ := by
      refine Set.Icc_eq_empty ?_
      unfold rTobs
      linarith only [not_le.1 htime]
    unfold EnergySolutionAt strongEnergy
    rw [hemp]
    simp
  obtain ⟨hDα, hDq, hDΛ, -, hstream, hband, -⟩ := c.data
  have hq1 : 1 < c.D.q := hDq ▸ X.hq.1
  have hΛ' : 128 ≤ A.Λ := hΛD.trans hΛ
  have hΛD' : 128 ≤ c.D.Λ := hDΛ ▸ hΛ'
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ'
  have hcr1 : cr = 1 := x.one
  have hkey : ∀ y : ℝ, cr * y = y := fun y => by rw [hcr1, one_mul]
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (le_trans (by norm_num) hΛD')
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos hΛ1 X.hζ hband (Nat.sub_le M 1)
  have hρ : 0 < c.D.termRho cr M := by
    show 0 < cr * _
    rw [hkey]
    exact Real.sqrt_pos.2 (mul_pos hν hh)
  have hεM : 0 < c.D.eps M := (Scales.epsilon_basic hq1 hΛD').1
  have hεM1 : 0 < c.D.eps (M - 1) := (Scales.epsilon_basic hq1 hΛD').1
  have hπT : ∀ v, 0 < (c.Gt'.retained M 1 A.RT).mass c.lawT v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD' c.lawT v.1
  have hπW : ∀ v, 0 ≤ c.Gw.mass c.lawW v := fun v =>
    (Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD' c.lawW v.1).le
  have hroots : ∀ v : CompIn c.Gw.comps, v.1.births = [] := c.weak.2.2.2.2.1
  have hwidth := kernelOf_width_pos (A.Pt c.D Cw cr M) (c.D.termRW A.σw M)
    (c.D.termRNew cr A.tT M) nW A.nT (Real.rpow_pos_of_pos hεM _)
    (mul_pos hρ (Real.rpow_pos_of_pos hεM1 _)) (c.Gt'.retained M 1 A.RT)
  obtain ⟨seed, rootM, rootR, seedKc, ι, -, -, hret⟩ := c.seed
  obtain ⟨aD, lam, haD, hlam, hsm, hst, -, hjets, -⟩ :=
    hdr A.Λ hΛ c.D.Φ hstream M c.D.κ hband M hM le_rfl (c.D.κ M) (c.D.κ (M - 1)) rfl rfl
  have hH : c.D.termH M = ocTauPP X.α X.q A.Λ M := by
    show ocTauPP c.D.α c.D.q c.D.Λ M = _
    rw [hDα, hDq, hDΛ]
  have hB₀0 : 0 ≤ B₀ := le_trans zero_le_one hB₀
  have hsqrt : c.D.termRho cr M ≤ Real.sqrt (c.D.κ (M - 1) * c.D.termH M) := by
    show cr * _ ≤ _
    rw [hkey]
    exact le_rfl
  have hsmall : B₀ * c.D.termRho cr M / lam ≤ 1 / 2 := by
    refine le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hB₀0)
      hlam.le) ?_
    rw [hH]
    exact hsm
  have hstrain : aD * B₀ * c.D.termRho cr M ^ 2 ≤ c.D.κ (M - 1) / 8 := by
    refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ.le hsqrt 2)
      (mul_nonneg haD hB₀0)) ?_
    rw [hH]
    exact hst
  have hjets' : ∀ t ∈ Set.Icc c.tp (c.a + A.T₀), ∀ l, 1 ≤ l → l ≤ A.Khat Kout → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel (c.D.Φ (M - 1)) t)) l x‖ ≤
        aD * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l) :=
    fun t _ l hl _ x => hjets l hl t x
  have hg : c.Z₀ = terminalTrace c.Gw (c.Gt'.retained M 1 A.RT) (c.Pterm fun v => c.V v c.aM) := by
    funext v'
    by_cases hv : v'.1 ∈ c.Gw.comps
    · rw [c.trace.1 v' hv]
      simp only [terminalTrace, hv, ↓reduceDIte]
    · rw [c.trace.2 v' hv]
      simp only [terminalTrace, hv, ↓reduceDIte]
  have hinit : weightedNorm (c.D.termRho cr M) ((c.Gt'.retained M 1 A.RT).mass c.lawT)
      (fun _ => 1) c.Z₀ ≤ max CP 0 * c.normF := by
    rw [hg]
    refine (terminalTrace_weightedNorm_le c.Gw _ c.lawW c.lawT _ _
      (fun v' hv => terminal_old_mass hroots c.law.1 v' hv) hπW).trans ?_
    exact c.prepB.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  have hE := Construction.Preservation.FullLift.native_reg_solution_strongEnergy_of_initial_norm
    (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ A.hφ₀ (c.Gt'.retained M 1 A.RT)
    c.lawT
    (retainedOperator c.lawT (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀ A.hφ₀ cker M
      (A.Khat Kout) cr c.tp (c.a + A.T₀) (c.Gt'.retained M 1 A.RT) hret htime hρ hν
      (le_max_left _ _) hπT hwidth) rfl rfl rfl (c.D.hΦ (M - 1)) aD B₀ lam haD hB₀ hlam hsmall
    hstrain hjets' c.Z₀ c.Z c.Zw c.Zk c.sol (fun _ => 1) (by funext v; simp [retainedOperator]) _
    hinit
  have hπfun : (fun v => (c.Gt'.retained M 1 A.RT).mass c.lawT v / (fun _ => (1 : ℝ)) v ^ 2) =
      (c.Gt'.retained M 1 A.RT).mass c.lawT := by
    funext v
    simp
  rw [hπfun] at hE
  have hρe : rRho c = c.D.termRho cr M := by
    simp only [rRho, OCData.termRho, OCData.termB, OCData.termH, hkey]
  have hTe : c.tp + rTobs c = c.a + A.T₀ := by
    unfold rTobs
    ring
  unfold EnergySolutionAt
  rw [hρe, hTe]
  refine hE.trans (le_of_eq ?_)
  congr 1
  unfold TermResCtx.normF
  ring

end AVRegularity.EntryTerminal.Ingredients.Recon.Energy
end
end

section
/-! # The chain at a context

Readout lemmas: `succReadout` commutes with truncation, preserves square integrability and
continuity in time. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.FullLift
open scoped ENNReal

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Energy

/-- Truncation commutes with a cast along an equality of roots. -/
theorem truncate_cast_root {K : ℕ} {r r' : ℕ} (e : r = r') (x : TorusHk (K + 1) (ScalarH r)) :
    truncateTorusHk (Nat.le_succ K)
        (cast (congrArg (fun r => TorusHk (K + 1) (ScalarH r)) e) x) =
      cast (congrArg (fun r => TorusHk K (ScalarH r)) e) (truncateTorusHk (Nat.le_succ K) x) := by
  subst e
  rfl

/-- The readout commutes with truncation. -/
theorem truncate_succReadout {S S' : Finset Comp} (m : ℕ) (E η : ℝ) {K : ℕ}
    (X : ∀ v' : CompIn S', TorusHk (K + 1) (ScalarH v'.1.root)) (v : CompIn S) :
    truncateTorusHk (Nat.le_succ K) (succReadout m E η (K + 1) X v) =
      succReadout m E η K (fun v' => truncateTorusHk (Nat.le_succ K) (X v')) v := by
  unfold succReadout
  rw [map_sum]
  refine Finset.sum_congr rfl fun v' _ => ?_
  by_cases h : compParent m v'.1 = v.1
  · simp only [h, dite_true]
    rw [ContinuousLinearMap.map_smul,
      truncate_cast_root ((compParent_root m v'.1).symm.trans (congrArg Comp.root h))]
  · simp only [h, dite_false, ContinuousLinearMap.map_zero]

/-- A cast along an equality of roots preserves square integrability. -/
theorem memLp_cast_root {K : ℕ} {r r' : ℕ} (e : r = r') {ν : Measure ℝ}
    {f : ℝ → TorusHk K (ScalarH r)} (hf : MemLp f 2 ν) :
    MemLp (fun t => cast (congrArg (fun r => TorusHk K (ScalarH r)) e) (f t)) 2 ν := by
  subst e
  exact hf

/-- A cast along an equality of roots preserves continuity. -/
theorem continuousOn_cast_root {K : ℕ} {r r' : ℕ} (e : r = r') {s : Set ℝ}
    {f : ℝ → TorusHk K (ScalarH r)} (hf : ContinuousOn f s) :
    ContinuousOn (fun t => cast (congrArg (fun r => TorusHk K (ScalarH r)) e) (f t)) s := by
  subst e
  exact hf

/-- The summand of the readout. -/
def readoutTerm {S S' : Finset Comp} (m : ℕ) (E η : ℝ) {K : ℕ} (v : CompIn S) (v' : CompIn S')
    (x : TorusHk K (ScalarH v'.1.root)) : TorusHk K (ScalarH v.1.root) :=
  if h : compParent m v'.1 = v.1 then
    (E ^ (η * ((compWord m v'.1).length : ℝ))) •
      cast (congrArg (fun r => TorusHk K (ScalarH r))
        ((compParent_root m v'.1).symm.trans (congrArg Comp.root h))) x
  else 0

theorem succReadout_eq_sum {S S' : Finset Comp} (m : ℕ) (E η : ℝ) {K : ℕ}
    (X : ∀ v' : CompIn S', TorusHk K (ScalarH v'.1.root)) (v : CompIn S) :
    succReadout m E η K X v = ∑ v' : CompIn S', readoutTerm m E η v v' (X v') := rfl

/-- The readout preserves square integrability in time. -/
theorem memLp_succReadout {S S' : Finset Comp} (m : ℕ) (E η : ℝ) {K : ℕ} {ν : Measure ℝ}
    (X : ∀ v' : CompIn S', ℝ → TorusHk K (ScalarH v'.1.root)) (hX : ∀ v', MemLp (X v') 2 ν)
    (v : CompIn S) : MemLp (fun t => succReadout m E η K (fun v' => X v' t) v) 2 ν := by
  have key : ∀ v' ∈ (Finset.univ : Finset (CompIn S')),
      MemLp (fun t => readoutTerm m E η v v' (X v' t)) 2 ν := by
    intro v' _
    unfold readoutTerm
    by_cases h : compParent m v'.1 = v.1
    · simp only [h, dite_true]
      exact (memLp_cast_root ((compParent_root m v'.1).symm.trans (congrArg Comp.root h))
        (hX v')).const_smul (E ^ (η * ((compWord m v'.1).length : ℝ)))
    · simp only [h, dite_false]
      have := ((0 : TorusHk K (ScalarH v'.1.root) →L[ℝ] TorusHk K (ScalarH v.1.root)).lipschitzWith).comp_memLp
        (ContinuousLinearMap.map_zero _) (hX v')
      convert this using 1
      funext t
      rfl
  have := memLp_finsetSum (f := fun v' t => readoutTerm m E η v v' (X v' t)) Finset.univ key
  simpa only [succReadout_eq_sum] using this

/-- The readout preserves continuity in time. -/
theorem continuousOn_succReadout {S S' : Finset Comp} (m : ℕ) (E η : ℝ) {K : ℕ} {s : Set ℝ}
    (X : ∀ v' : CompIn S', ℝ → TorusHk K (ScalarH v'.1.root)) (hX : ∀ v', ContinuousOn (X v') s)
    (v : CompIn S) : ContinuousOn (fun t => succReadout m E η K (fun v' => X v' t) v) s := by
  have key : ∀ v' ∈ (Finset.univ : Finset (CompIn S')),
      ContinuousOn (fun t => readoutTerm m E η v v' (X v' t)) s := by
    intro v' _
    unfold readoutTerm
    by_cases h : compParent m v'.1 = v.1
    · simp only [h, dite_true]
      exact (continuousOn_cast_root ((compParent_root m v'.1).symm.trans (congrArg Comp.root h))
        (hX v')).const_smul (E ^ (η * ((compWord m v'.1).length : ℝ)))
    · simp only [h, dite_false]
      exact continuousOn_const
  have := continuousOn_finsetSum (f := fun v' t => readoutTerm m E η v v' (X v' t))
    Finset.univ key
  simpa only [succReadout_eq_sum] using this

open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
  AVRegularity.CycleComparison.Coarse

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
    Ce cker j₀ M)

open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
  AVRegularity.CycleComparison.Coarse in
/-- **Continuity of the coarse field on the window.** -/
theorem reconW_continuousOn (kc : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (hcovc : ContinuousOn (fun t => termCovPrimitive c.D M c.tp t) (Set.Icc c.tp (c.a + A.T₀)))
    (hcont : ∀ v', ContinuousOn (c.Z v') (Set.Icc c.tp (c.a + A.T₀)))
    (v : CompIn c.Gw.comps) : ContinuousOn (reconW c kc hW v) (Set.Icc c.tp (c.a + A.T₀)) := by
  have hK2 : A.Khat Kout - 2 * A.pT + 2 * A.pT ≤ A.Khat Kout := by omega
  have hH : ∀ i j, ContinuousOn (fun t => termCovPrimitive c.D M c.tp t i j)
      (Set.Icc c.tp (c.a + A.T₀)) := fun i j =>
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hcovc)
  have hAc := CycleComparison.Reconstruction.covPolyP_adj_continuousOn (E := ScalarH v.1.root)
    (fun t => termCovPrimitive c.D M c.tp t) (fun t => covBound (termCovPrimitive c.D M c.tp t))
    (fun _ => le_rfl) hH A.pT 0 (A.Khat Kout) (A.Khat Kout - 2 * A.pT) hK2
  have hZc := continuousOn_succReadout (S := c.Gw.comps) M (c.D.eps (M - 1)) A.η₀ c.Z hcont v
  have hcast : ContinuousOn (fun t => torusCast (E := ScalarH v.1.root)
      (by omega : A.Khat Kout = A.Khat Kout - 2 * A.pT + 2 * A.pT) (eZr c v t))
      (Set.Icc c.tp (c.a + A.T₀)) :=
    (torusCast (E := ScalarH v.1.root)
      (by omega : A.Khat Kout = A.Khat Kout - 2 * A.pT + 2 * A.pT)).continuous.comp_continuousOn hZc
  have hmain := (truncateTorusHk (E := ScalarH v.1.root) hW).continuous.comp_continuousOn
    (hAc.clm_apply hcast)
  refine hmain.congr fun t ht => ?_
  have hPZ := (c.lift.2.1 v t ht).1
  have hadj : IsCovImage (AVRegularity.covPolyP (termCovPrimitive c.D M c.tp t) A.pT)
      (eZr c v t) ((TorusAdj.covPolyP (E := ScalarH v.1.root) (termCovPrimitive c.D M c.tp t)
        le_rfl A.pT 0 (A.Khat Kout)).adj (A.Khat Kout - 2 * A.pT) hK2
        (torusCast (by omega : A.Khat Kout = A.Khat Kout - 2 * A.pT + 2 * A.pT) (eZr c v t))) := by
    intro φ hφ hp
    have hid := (TorusAdj.covPolyP (E := ScalarH v.1.root) (termCovPrimitive c.D M c.tp t)
      le_rfl A.pT 0 (A.Khat Kout)).ident (A.Khat Kout - 2 * A.pT) hK2
      (torusCast (by omega : A.Khat Kout = A.Khat Kout - 2 * A.pT + 2 * A.pT) (eZr c v t)) φ
      (hφ.of_le (by exact_mod_cast le_top)) hp
    change cellInner (tval _) φ = cellInner (tval (eZr c v t)) _
    rw [hid, tval_torusCast]
  have heq := covImage_unique _ _ _ _ hPZ hadj
  show truncateTorusHk hW (c.PZ v t) = _
  rw [heq]
  rfl

open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
  AVRegularity.CycleComparison.Coarse in
/-- **The chain at a context.** -/
theorem energyChain : EnergyChainStatement := by
  intro X A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x
    kc ℓ hW hΛ hM hkc hlarge
  have hTe : c.tp + rTobs c = c.a + A.T₀ := by
    unfold rTobs
    ring
  by_cases htime : c.tp ≤ c.a + A.T₀
  swap
  · have hemp : Set.Icc c.tp (c.tp + rTobs c) = ∅ := by
      refine Set.Icc_eq_empty ?_
      unfold rTobs
      linarith only [not_le.1 htime]
    refine ⟨fun v => ?_, ?_⟩
    · rw [hemp]
      exact continuousOn_empty _
    · unfold strongEnergyUpTo
      rw [hemp]
      simp
  obtain ⟨hcov, hcovc, hent⟩ := hlarge
  rw [hTe] at hcov hcovc ⊢
  obtain ⟨hDα, hDq, hDΛ, -, hstream, hband, -⟩ := c.data
  have hq1 : 1 < c.D.q := hDq ▸ X.hq.1
  have hΛD : 128 ≤ c.D.Λ := hDΛ ▸ hΛ
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos hΛ1 X.hζ hband (Nat.sub_le M 1)
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (le_trans (by norm_num) hΛD)
  have hρ : 0 < rRho c := Real.sqrt_pos.2 (mul_pos hν hh)
  have hπW : ∀ v, 0 < c.Gw.mass c.lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD c.lawW v.1
  have hπT : ∀ w, 0 < (c.Gt'.retained M 1 A.RT).mass c.lawT w := fun w =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD c.lawT w.1
  have hsol := c.sol
  unfold GenStage.IsRegSolution at hsol
  obtain ⟨hcont, hmem, hae, -⟩ := hsol
  have hroots : ∀ v : CompIn c.Gw.comps, v.1.births = [] := c.weak.2.2.2.2.1
  have hlevel : c.Gw.level = M := c.weak.2.2.1
  have hold : ∀ v ∈ c.Gw.comps, ∀ e ∈ v.births, M ≤ e.scale := by
    intro v hv e he
    exact absurd he (by rw [hroots ⟨v, hv⟩]; simp)
  have hsub := retained_comps_subset_succExt c.succ hlevel
  have hM1 : 1 ≤ M := hM
  -- the readout step
  have hread : strongEnergy (rRho c) (c.D.κ (M - 1)) (c.Gw.mass c.lawW) c.tp (c.a + A.T₀)
      (eZr c) (eZrw c) ≤
      ENNReal.ofReal (Real.sqrt ((wordsUpTo A.alph (A.RT + 1)).card + 1)) *
        strongEnergy (rRho c) (c.D.κ (M - 1)) ((c.Gt'.retained M 1 A.RT).mass c.lawT)
          c.tp (c.a + A.T₀) c.Z c.Zw := by
    have hE0 : 0 ≤ c.D.eps (M - 1) := (Scales.epsilon_basic hq1 hΛD).1.le
    exact readout_strongEnergy_of_diagonal_entries (S := c.Gw.comps)
      (S' := (c.Gt'.retained M 1 A.RT).comps) M (c.D.eps (M - 1)) A.η₀ (rRho c)
      (c.D.κ (M - 1)) c.tp (c.a + A.T₀) (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) hE0
      (by positivity) (c.Gw.mass c.lawW) ((c.Gt'.retained M 1 A.RT).mass c.lawT) hπW hπT
      (fun w => readout_parent_mem hM1 hold (hsub w.2)) hent
      (fun v => by exact_mod_cast readout_indexed_fiber_card_le hM1 hold hsub v.1)
      c.Z c.Zw hmem
  have hval : ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      IsCovImage (AVRegularity.covPolyP (termCovPrimitive c.D M c.tp t) A.pT) (eZr c v t)
        (reconW c kc hW v t) :=
    fun v t ht => covImage_truncate hW _ _ _ (c.lift.2.1 v t ht).1
  have hRw : ∀ v, MemLp (eZrw c v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀))) :=
    fun v => memLp_succReadout M _ _ c.Zw hmem v
  have hae' : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc c.tp (c.a + A.T₀))),
      truncateTorusHk (Nat.le_succ _) (eZrw c v t) = eZr c v t := by
    intro v
    have hall := ae_all_iff.2 hae
    filter_upwards [hall] with t ht
    simp only [eZrw, eZr]
    rw [truncate_succReadout]
    congr 1
    funext v'
    exact ht v'
  have hcost : ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      covPolyConst (fbCovConst (rRho c) (termCovPrimitive c.D M c.tp t)
        (kc + (A.NT + A.Dt) + 2 * A.pT)) A.pT ≤
      covPolyConst (4 * ((A.Khat Kout : ℕ) : ℝ) ^ 2) A.pT := by
    intro t ht
    have h1 := gfbCovConst_le hρ (termCovPrimitive c.D M c.tp t) (kc + (A.NT + A.Dt) + 2 * A.pT)
      (hcov t ht)
    have h2 : 4 * (((kc + (A.NT + A.Dt) + 2 * A.pT : ℕ)) : ℝ) ^ 2 ≤
        4 * ((A.Khat Kout : ℕ) : ℝ) ^ 2 := by
      have : kc + (A.NT + A.Dt) + 2 * A.pT ≤ A.Khat Kout := by omega
      have h3 : (((kc + (A.NT + A.Dt) + 2 * A.pT : ℕ)) : ℝ) ≤ ((A.Khat Kout : ℕ) : ℝ) := by
        exact_mod_cast this
      have h4 : (0 : ℝ) ≤ (((kc + (A.NT + A.Dt) + 2 * A.pT : ℕ)) : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact gfbCovPoly_mono (fbCovConst_nonneg hρ _ _) (h1.trans h2) A.pT
  have hCf : 0 ≤ covPolyConst (4 * ((A.Khat Kout : ℕ) : ℝ) ^ 2) A.pT :=
    Finset.sum_nonneg fun l _ => div_nonneg (pow_nonneg (by positivity) l) (Nat.cast_nonneg _)
  have hstep := energyCovStep (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root)
    (K := kc + 1 + (A.NT + A.Dt)) (K' := kc + (A.NT + A.Dt)) (p := A.pT) (L := A.Khat Kout)
    (m := rpord A ℓ) (by omega) hkc (by omega) hρ (fun t => termCovPrimitive c.D M c.tp t)
    (c.D.κ (M - 1)) c.tp (c.a + A.T₀) _ hCf (c.Gw.mass c.lawW) hπW (reconW c kc hW) (eZr c)
    (eZrw c) hRw hae' hval hcost
  refine ⟨?_, ?_⟩
  · exact fun v => reconW_continuousOn c kc hW hcovc hcont v
  · refine hstep.trans ?_
    calc _ ≤ ENNReal.ofReal (covPolyConst (4 * ((A.Khat Kout : ℕ) : ℝ) ^ 2) A.pT) *
          (ENNReal.ofReal (Real.sqrt ((wordsUpTo A.alph (A.RT + 1)).card + 1)) *
            strongEnergy (rRho c) (c.D.κ (M - 1)) ((c.Gt'.retained M 1 A.RT).mass c.lawT)
              c.tp (c.a + A.T₀) c.Z c.Zw) := mul_le_mul' le_rfl hread
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCf]

end AVRegularity.EntryTerminal.Ingredients.Recon.Energy

namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-- **The energy of the coarse field of the terminal reconstruction window.** -/
theorem termReconEnergy : TermReconEnergyStatement :=
  Energy.termReconEnergy_of_statements Energy.energyLarge Energy.energyChain Energy.energySolution

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end
