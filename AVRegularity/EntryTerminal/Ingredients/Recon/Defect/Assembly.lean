-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.Recon.Defect.Jets
import AVRegularity.Applications.TorusEnergy.StreamFacts
import AVRegularity.IterationPassage.Passage.Profiles.ClausesStatement
import AVRegularity.EntryWeak.IndependentFiniteLiftFieldReserve
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleComparison.QuietDecay.Partition.Main
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofFirstSourceConstGrade0
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseSum
import AVRegularity.CycleComparison.Coarse.Defect.DFBound
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

section
section
/-! **The defect from its smooth-test form, with square integrable `Fc`** (step (iv) of the conversion).

A version of `coarseDefect_of_witness` in which the
smooth-test identity is a hypothesis, the retained field is uniformly bounded (hypothesis) and the
coarse flux `Fc` only has `s ↦ ‖Fc v s‖` integrable on the window (the majorant of
`DefIntegrandBound`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse
  AVRegularity.CoupledEnergy.Galerkin
open Filter Topology

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

/-- **The coarse defect from the smooth-test identity** (`L²`-in-time `Fc`). -/
theorem CoarseDefectOfSmooth
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {f : ∀ v, TorusHk N (h v)}
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))} {MW : ℝ}
    (hMW : ∀ s ∈ Set.Icc t₀ t₁, ∀ v, ‖W v s‖ ≤ MW)
    (hFc : ∀ v, IntegrableOn (fun s => ‖Fc v s‖) (Set.Icc t₀ t₁))
    (hsm : ∀ v, ∀ t ∈ Set.Icc t₀ t₁, ∀ ψ : Vec 2 → h v, ContDiff ℝ (⊤ : ℕ∞) ψ →
      AVenhance.IsZ2Periodic ψ →
      IntegrableOn (fun s => ∫ x in AVenhance.unitCube,
        wIntegrand B b D H AD CE Jm W Fc v ψ s x) (Set.Ioc t₀ t) ∧
      cellInner (tval (W v t)) ψ - cellInner (fun x => (f v).toFunction.jet (valueIndex2 N) x) ψ =
        ∫ s in Set.Ioc t₀ t, ∫ x in AVenhance.unitCube,
          wIntegrand B b D H AD CE Jm W Fc v ψ s x) :
    AVRegularity.IsCoarseDefect t₀ t₁ B b D H k N AD CE Jm f W Fc := by
  intro v t ht φ
  obtain ⟨C, hC⟩ := DefIntegrandBound P hMW v
  have hIcc : ∀ s ∈ Set.Ioc t₀ t, s ∈ Set.Icc t₀ t₁ := fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  have hWm := memLp_jet (W v t) (valueIndex2 (k + 1 + D))
  have hfm := memLp_jet (f v) (valueIndex2 N)
  let Lf : TorusHk 1 (h v) → ℝ := fun φ =>
    (∫ x in AVenhance.unitCube, inner ℝ ((W v t).toFunction.jet (valueIndex2 (k + 1 + D)) x)
      (φ.toFunction.jet (valueIndex2 1) x)) -
    ∫ x in AVenhance.unitCube, inner ℝ ((f v).toFunction.jet (valueIndex2 N) x)
      (φ.toFunction.jet (valueIndex2 1) x)
  let Rf : ℝ → TorusHk 1 (h v) → ℝ := fun s φ =>
    ∫ x in AVenhance.unitCube, defIntegrand B b D H AD CE Jm W Fc v φ s x
  have hLsub : ∀ φ φ', Lf (φ - φ') = Lf φ - Lf φ' := fun φ φ' => by
    simp only [Lf]
    rw [integral_inner_jet_sub hWm φ φ', integral_inner_jet_sub hfm φ φ']
    ring
  have hLb : ∀ φ, |Lf φ| ≤ (‖W v t‖ + ‖f v‖) * ‖φ‖ := fun φ => by
    simp only [Lf]
    refine (abs_sub _ _).trans ?_
    rw [add_mul]
    exact add_le_add (abs_integral_inner_jet_le _ φ) (abs_integral_inner_jet_le _ φ)
  have hRsub : ∀ s ∈ Set.Ioc t₀ t, ∀ φ φ', Rf s (φ - φ') = Rf s φ - Rf s φ' :=
    fun s hs φ φ' => by
      simp only [Rf]
      rw [integral_congr_ae (defIntegrand_sub W Fc v φ φ' s)]
      exact integral_sub (hC s (hIcc s hs) φ).1 (hC s (hIcc s hs) φ').1
  have hm : IntegrableOn (fun s => C + 2 * ‖Fc v s‖) (Set.Ioc t₀ t) :=
    (integrableOn_const (measure_Ioc_lt_top).ne).add
      (((hFc v).mono_set (fun s hs => hIcc s hs)).const_mul 2)
  have hRb : ∀ s ∈ Set.Ioc t₀ t, ∀ φ, |Rf s φ| ≤ (C + 2 * ‖Fc v s‖) * ‖φ‖ := fun s hs φ =>
    (hC s (hIcc s hs) φ).2
  have hN : ∀ n, IntegrableOn (fun s => Rf s (galerkinProj n φ)) (Set.Ioc t₀ t) ∧
      Lf (galerkinProj n φ) = ∫ s in Set.Ioc t₀ t, Rf s (galerkinProj n φ) := fun n => by
    obtain ⟨hI, heq⟩ := hsm v t ht (approxField n φ) (approxField_contDiff n φ)
      (approxField_periodic n φ)
    have hR' : (fun s => Rf s (galerkinProj n φ)) = fun s =>
        ∫ x in AVenhance.unitCube, wIntegrand B b D H AD CE Jm W Fc v (approxField n φ) s x :=
      funext fun s => integral_congr_ae (defIntegrand_galerkin_ae B b D H AD CE Jm W Fc v φ n s)
    have hL' : Lf (galerkinProj n φ) =
        cellInner (tval (W v t)) (approxField n φ) -
          cellInner (fun x => (f v).toFunction.jet (valueIndex2 N) x) (approxField n φ) := by
      simp only [Lf, cellInner, tval]
      congr 1
      · refine integral_congr_ae ?_
        filter_upwards [galerkin_value_ae n φ] with x hx
        rw [hx]
      · refine integral_congr_ae ?_
        filter_upwards [galerkin_value_ae n φ] with x hx
        rw [hx]
    refine ⟨?_, ?_⟩
    · rw [hR']; exact hI
    · rw [hR', hL']; exact heq
  obtain ⟨hI, heq⟩ := IntegratedIdentityOfTendsto Lf Rf hLsub hLb hRsub
    (fun s => C + 2 * ‖Fc v s‖) hm hRb (galerkinProj_tendsto φ) hN
  exact ⟨integrable_inner_memLp hWm (memLp_jet φ _), integrable_inner_memLp hfm (memLp_jet φ _),
    fun s hs => (hC s (hIcc s hs) φ).1, hI, heq⟩

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Integration by parts on the torus for Hilbert-valued fluxes** (for the macro swap).

For a `C¹` periodic flux `G : Vec 2 → Fin 2 → E` and a `C¹` periodic test `φ : Vec 2 → E`,
`∫_{𝕋²} ∑_k ⟨G_k, ∂_kφ⟩ = -∫_{𝕋²} ⟨div G, φ⟩`.

Degenerate cases:
- `E = ℝ`, `φ = 1`: both sides vanish (`integral_div_periodic`).
- `G = ∇ψ`: the Green identity on the torus. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVenhance

namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-- The integrand of the integration by parts, pointwise. -/
theorem s117ibp_pointwise {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : Vec 2 → Fin 2 → E) (φ : Vec 2 → E) (hG : ∀ k, ContDiff ℝ 1 (fun y => G y k))
    (hφ : ContDiff ℝ 1 φ) (x : Vec 2) :
    fderiv ℝ (fun y => inner ℝ (G y 0) (φ y)) x (basisVec 0) +
        fderiv ℝ (fun y => inner ℝ (G y 1) (φ y)) x (basisVec 1) =
      inner ℝ (divE G x) (φ x) + ∑ k : Fin 2, inner ℝ (G x k) (gradE φ x k) := by
  have hd : ∀ k : Fin 2, DifferentiableAt ℝ (fun y => G y k) x := fun k =>
    ((hG k).differentiable (by simp)) x
  have hp : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)) x
  rw [fderiv_inner_apply ℝ (hd 0) hp, fderiv_inner_apply ℝ (hd 1) hp]
  simp only [divE, gradE, Fin.sum_univ_two, inner_add_left]
  ring

/-- **Torus integration by parts.** -/
theorem torus_ibp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : Vec 2 → Fin 2 → E) (φ : Vec 2 → E) (hG : ∀ k, ContDiff ℝ 1 (fun y => G y k))
    (hGp : ∀ k, IsZ2Periodic (fun y => G y k)) (hφ : ContDiff ℝ 1 φ) (hφp : IsZ2Periodic φ) :
    ∫ y in unitCube, ∑ k : Fin 2, inner ℝ (G y k) (gradE φ y k) =
      -∫ y in unitCube, inner ℝ (divE G y) (φ y) := by
  have hF : ∀ k, ContDiff ℝ 1 (fun y => inner ℝ (G y k) (φ y)) := fun k => (hG k).inner ℝ hφ
  have hFp : ∀ k, IsZ2Periodic (fun y => inner ℝ (G y k) (φ y)) := fun k n x => by
    show inner ℝ (G (x + latticeShift n) k) (φ (x + latticeShift n)) = _
    have h1 : G (x + latticeShift n) k = G x k := hGp k n x
    have h2 : φ (x + latticeShift n) = φ x := hφp n x
    rw [h1, h2]
  have h0 := AVRegularity.Applications.integral_div_periodic (hF 0) (hF 1) (hFp 0) (hFp 1)
  have hGc : ∀ k, Continuous fun y => fderiv ℝ (fun y => G y k) y := fun k =>
    (hG k).continuous_fderiv (by simp)
  have hφc : Continuous fun y => fderiv ℝ φ y := hφ.continuous_fderiv (by simp)
  have hGcont : ∀ k, Continuous fun y => G y k := fun k => (hG k).continuous
  have c1 : Continuous fun y => inner ℝ (divE G y) (φ y) := by
    refine Continuous.inner ?_ hφ.continuous
    unfold divE
    exact continuous_finsetSum _ fun j _ => (hGc j).clm_apply continuous_const
  have c2 : Continuous fun y => ∑ k : Fin 2, inner ℝ (G y k) (gradE φ y k) := by
    refine continuous_finsetSum _ fun k _ => (hGcont k).inner ?_
    exact hφc.clm_apply continuous_const
  have e : ∀ x, fderiv ℝ (fun y => inner ℝ (G y 0) (φ y)) x (basisVec 0) +
        fderiv ℝ (fun y => inner ℝ (G y 1) (φ y)) x (basisVec 1) =
      inner ℝ (divE G x) (φ x) + ∑ k : Fin 2, inner ℝ (G x k) (gradE φ x k) :=
    fun x => s117ibp_pointwise G φ hG hφ x
  simp only [e] at h0
  rw [integral_add (AVRegularity.Applications.integrableOn_cube_of_continuous c1)
    (AVRegularity.Applications.integrableOn_cube_of_continuous c2)] at h0
  linarith

/-- The pairing of a `C¹` flux with the gradient of a `C¹` test is integrable on the cell. -/
theorem pairing_integrable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : Vec 2 → Fin 2 → E) (φ : Vec 2 → E) (hG : ∀ k, ContDiff ℝ 1 (fun y => G y k))
    (hφ : ContDiff ℝ 1 φ) :
    Integrable (fun y => ∑ k : Fin 2, inner ℝ (G y k) (gradE φ y k))
      (volume.restrict unitCube) := by
  have hφc : Continuous fun y => fderiv ℝ φ y := hφ.continuous_fderiv (by simp)
  refine AVRegularity.Applications.integrableOn_cube_of_continuous ?_
  exact continuous_finsetSum _ fun k _ => (hG k).continuous.inner (hφc.clm_apply continuous_const)

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Smoothness of the root flux defect** (generic in the stages).

`rootFluxDefect_smooth`: the root flux defect of a field `aZ` of class `C^{n+D_m}` is `C^n` and
`ℤ²`-periodic when the coefficients of `G'` are. Same proof as `omittedFluxClassical_smooth`, with
the field `aZ - S aZ` in place of `S aY`.

Degenerate cases: `aZ = 0` (everything is zero); no row `u'` of `G'` lies in `G` (the sum is empty,
the defect is `0`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation

section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- **The root flux defect is smooth and periodic.** -/
theorem rootFluxDefect_smooth (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    (G G' : GenStage D hr Dm bw j₀) (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (t : ℝ) (n : ℕ)
    (hcoef : ∀ (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) (d : ℕ),
      ContDiff ℝ (n : ℕ) (G'.physCoeff v u γ d t) ∧ IsZ2Periodic (G'.physCoeff v u γ d t))
    (haZ : ∀ u : CompIn G.comps, ContDiff ℝ ((n + Dm : ℕ) : ℕ∞) (fun y => aZ t y u) ∧
      IsZ2Periodic (fun y => aZ t y u)) (v : CompIn G'.comps) :
    ContDiff ℝ (n : ℕ) (fun x => rootFluxDefect P seedK freshK φ₀ G G' aZ v t x) ∧
      IsZ2Periodic (fun x => rootFluxDefect P seedK freshK φ₀ G G' aZ v t x) := by
  classical
  have term : ∀ (u : CompIn G'.comps) (hu : u.1 ∈ G.comps) (γ : G'.fam.Γ v u) (d : ℕ), d ≤ Dm →
      ContDiff ℝ (n : ℕ) (fun x => G'.physCoeff v u γ d t x (WithLp.toLp 2
        fun word : DerivativeWord2 (d - 1) =>
          orderedDerivative word (fun y => aZ t y ⟨u.1, hu⟩ -
            (G'.kernelOf P seedK freshK v u γ).applyClassical φ₀ t
              (fun y' => aZ t y' ⟨u.1, hu⟩) y) x)) ∧
      IsZ2Periodic (fun x => G'.physCoeff v u γ d t x (WithLp.toLp 2
        fun word : DerivativeWord2 (d - 1) =>
          orderedDerivative word (fun y => aZ t y ⟨u.1, hu⟩ -
            (G'.kernelOf P seedK freshK v u γ).applyClassical φ₀ t
              (fun y' => aZ t y' ⟨u.1, hu⟩) y) x)) := by
    intro u hu γ d hd
    obtain ⟨h1, h2⟩ := haZ ⟨u.1, hu⟩
    have hK := AVRegularity.IterationPassage.Passage.regularKernel_contDiff_periodic hφs hφsupp
      (G'.kernelOf P seedK freshK v u γ) t h1 h2
    have hDf : ContDiff ℝ ((n + Dm : ℕ) : ℕ∞) (fun y => aZ t y ⟨u.1, hu⟩ -
        (G'.kernelOf P seedK freshK v u γ).applyClassical φ₀ t
          (fun y' => aZ t y' ⟨u.1, hu⟩) y) := h1.sub hK.1
    have hDp : IsZ2Periodic (fun y => aZ t y ⟨u.1, hu⟩ -
        (G'.kernelOf P seedK freshK v u γ).applyClassical φ₀ t
          (fun y' => aZ t y' ⟨u.1, hu⟩) y) := fun m x => by
      simp only [h2 m x, hK.2 m x]
    refine ⟨?_, ?_⟩
    · refine (hcoef v u γ d).1.clm_apply ?_
      refine PiLp.contDiff_toLp.comp (contDiff_pi.2 fun word => ?_)
      exact ChartTransport.contDiff_orderedDerivative (p := n) (q := d - 1) word
        (hDf.of_le (by exact_mod_cast (by omega : n + (d - 1) ≤ n + Dm)))
    · intro m x
      have e1 := (hcoef v u γ d).2 m x
      have e2 : ∀ word : DerivativeWord2 (d - 1), orderedDerivative word
          (fun y => aZ t y ⟨u.1, hu⟩ - (G'.kernelOf P seedK freshK v u γ).applyClassical φ₀ t
            (fun y' => aZ t y' ⟨u.1, hu⟩) y) (x + latticeShift m) = orderedDerivative word
          (fun y => aZ t y ⟨u.1, hu⟩ - (G'.kernelOf P seedK freshK v u γ).applyClassical φ₀ t
            (fun y' => aZ t y' ⟨u.1, hu⟩) y) x :=
        fun word => ChartTransport.isZ2Periodic_orderedDerivative word hDp m x
      simp only [e1, e2]
  constructor
  · unfold rootFluxDefect
    refine ContDiff.sum fun u _ => ?_
    by_cases hu : u.1 ∈ G.comps
    · simp only [hu, dite_true]
      refine ContDiff.sum fun γ _ => ?_
      refine ContDiff.sum fun d _ => ?_
      exact (term u hu γ d.1 (Finset.mem_Icc.1 d.2).2).1
    · simp only [hu, dite_false]; exact contDiff_const
  · intro m x
    unfold rootFluxDefect
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u.1 ∈ G.comps
    · simp only [hu, dite_true]
      refine Finset.sum_congr rfl fun γ _ => ?_
      refine Finset.sum_congr rfl fun d _ => ?_
      exact (term u hu γ d.1 (Finset.mem_Icc.1 d.2).2).2 m x
    · simp only [hu, dite_false]

end Generic

end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! **The cell-mean identity at a lift setting** (glued mean, step (i)).

`cellMean_liftFluxX_eq`: at a lift setting with a lift sequence of box orders `≥ D`, the cell
mean of the slow lift flux `liftFluxX` of positive grade is the action of the positive mean-flux
coefficient. This is `positiveMeanFluxCoefficient_literal_apply` (`EntryWeakProofs`) with its
regularity hypotheses discharged from `IsLiftSetting` and `IsLiftSequence`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι (fun _ => ℝ) D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}

omit [DecidableEq ι] in
/-- A lift action of box smooth coefficients on a smooth field is box smooth and periodic, hence
a good field of any order up to the box orders. -/
theorem goodField_liftApply {sX sZ : ℕ} (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (hh q r : ℕ) (hr : r ≤ sX) (hr' : r ≤ sZ) (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ)
    (hbox : ∀ m α v u, IsBoxSmooth sX sZ (fun X z => Cc hh q m α t X z v u))
    (hper : ∀ X m α v u, AVenhance.IsZ2Periodic (fun z => Cc hh q m α t X z v u)) :
    GoodField r (liftApply q (Cc hh q) (fun _ => f) t) := by
  have hb : IsBoxSmooth sX sZ (liftApply q (Cc hh q) (fun _ => f) t) :=
    AVRegularity.CycleComparison.Lift.isBoxSmooth_pi sX sZ _ fun v =>
      QuietDecay.Partition.isBoxSmooth_liftApply q sX sZ (Cc hh q) _ t (fun m α v' u => hbox m α v' u)
        (hf.of_le (by exact_mod_cast le_top)) v
  exact ⟨hb.contDiff_uncurry hr hr', fun X =>
    AVRegularity.CycleComparison.Reconstruction.liftApply_isZ2Periodic q (Cc hh q) _ t X
      (fun m α v u => hper X m α v u)⟩

variable
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **The cell-mean identity**: the cell mean of the positive-grade slow lift
flux is the action of the positive mean-flux coefficient. -/
theorem cellMean_liftFluxX_eq (sX sZ : ℕ) (hX : D ≤ sX) (hZ : D ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k₀ : Fin 2) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    liftApply (n - 1) (positiveMeanFluxCoefficient Q Cc hh n k₀) (fun _ => f) t X z v =
      fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) hh n t X z k₀) v := by
  have hD2 := P.D_ge
  have hN1 := P.N_ge
  have hb : ∀ hh', hh' ≤ H → ∀ q m α v u, IsBoxSmooth sX sZ
      (fun X z => Cc hh' q m α t X z v u) := fun hh' h' q m α v u =>
    (hseq.2.2.2.2.2.1 hh' h' q m α v u t ht).1
  have hp : ∀ hh', hh' ≤ H → ∀ q X m α v u, AVenhance.IsZ2Periodic
      (fun z => Cc hh' q m α t X z v u) := fun hh' h' q X m α v u =>
    (hseq.2.2.2.2.2.1 hh' h' q m α v u t ht).2 X
  have hgood1 : ∀ hh' q, hh' ≤ H → ∀ r, r ≤ D →
      GoodField r (liftApply q (Cc hh' q) (fun _ => f) t) := fun hh' q h' r hr =>
    goodField_liftApply Cc hh' q r (hr.trans hX) (hr.trans hZ) f hf t (hb hh' h' q)
      (fun X m α v u => hp hh' h' q X m α v u)
  have hΨmean : ∀ X', fieldCellMean (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => f) t X') = 0 := by
    intro X'
    by_cases h0 : n - 2 = 0
    · have : liftApply (n - 2) (Cc hh (n - 2)) (fun _ => f) t = fun _ _ => 0 :=
        liftApply_eq_zero_of_coeff _ _ (fun m α t X z v u => by
          rw [h0]; exact hseq.2.1 hh hhpos hhh m α t X z v u) _ _
      rw [this]; exact fieldCellMean_zero
    · by_cases hle : n - 2 ≤ N
      · exact liftApply_fieldCellMean_eq_zero Q sX sZ a b N H Cc hseq hh hhh (n - 2)
          (by omega) hle f hf t ht X'
      · have : liftApply (n - 2) (Cc hh (n - 2)) (fun _ => f) t = fun _ _ => 0 :=
          liftApply_eq_zero_of_coeff _ _ (fun m α t X z v u =>
            hseq.2.2.1 hh hhh (n - 2) (by omega) m α t X z v u) _ _
        rw [this]; exact fieldCellMean_zero
  refine (positiveMeanFluxCoefficient_literal_apply Q (by omega) Cc hh n hn (by omega) f hf k₀
    t X z v ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · intro i j
    exact (P.G_smooth t ht i j).of_le (by exact_mod_cast Nat.zero_le qs)
  · exact setting_drift_continuous P t ht
  · exact hgood1 hh (n - 1) hhh 1 (by omega)
  · exact ⟨hgood1 hh (n - 2) hhh 1 (by omega), fun _ X' => hΨmean X'⟩
  · intro m hm α u
    exact ((hb hh hhh (n - 1) m α v u).1 X).continuous
  · intro j hj m hm α u u'
    exact (hb (hh - 1) (by omega) (n - 1 - j) m α u u').mono (by omega) (by omega)
  · intro q
    exact hgood1 (hh - 1) q (by omega) D le_rfl
  · intro v u d γ hγ α
    have hbs := P.coeff_smooth v u d γ hγ α t ht
    have hqs : 1 ≤ qs := by
      have h1 : 0 < N + D := by omega
      have h2 : 0 < 4 * (H + 1) * (N + D) ^ 2 := by positivity
      rw [P.qs_eq]; omega
    have hqf : 1 ≤ qf := by rw [P.qf_eq]; omega
    exact ⟨hbs.contDiff_uncurry hqs hqf, fun X => γ.periodic α t X⟩

include P in
/-- **The cell-mean identity at grade zero**: the cell mean of the grade-zero slow lift flux is the
action of the diagonal mean-flux coefficient. -/
theorem diag_cellMean_liftFluxX_eq (sX sZ : ℕ) (hX : 1 ≤ sX) (hZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (n : ℕ) (hn : 2 ≤ n) (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k₀ : Fin 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftApply (n - 1) (diagonalMeanFluxCoefficient Q Cc n k₀) (fun _ => f) t X z =
      fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) 0 n t X z k₀) := by
  have hb : ∀ q m α v u, IsBoxSmooth sX sZ (fun X z => Cc 0 q m α t X z v u) :=
    fun q m α v u => (hseq.2.2.2.2.2.1 0 (Nat.zero_le H) q m α v u t ht).1
  have hgood : ∀ q, GoodField 1 (liftApply q (Cc 0 q) (fun _ => f) t) := fun q =>
    goodField_liftApply Cc 0 q 1 hX hZ f hf t (hb q)
      (fun X m α v u => (hseq.2.2.2.2.2.1 0 (Nat.zero_le H) q m α v u t ht).2 X)
  have hΦ := hgood (n - 1)
  have hΨ := hgood (n - 2)
  set Φ := liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t with hΦdef
  set Ψ := liftApply (n - 2) (Cc 0 (n - 2)) (fun _ => f) t with hΨdef
  have hΦX : ContDiff ℝ 1 (Φ X) := by
    have := hΦ.1.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ _ (fun z : Vec 2 => (X, z)))
    exact this
  have hcΦ : Continuous (Φ X) := hΦX.continuous
  have hfast : ∀ j : Fin 2, fieldCellMean (fun z => fastPartial j Φ X z) = 0 := fun j =>
    fieldCellMean_fastPartial_eq_zero (Φ X) hΦX (hΦ.2 X) j
  have hcfast : ∀ j : Fin 2, Continuous (fun z => fastPartial j Φ X z) := fun j =>
    (hΦX.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcslow : ∀ j : Fin 2, Continuous (fun z => slowPartial j Ψ X z) := by
    intro j
    have := continuous_fderiv_slow_of_contDiff hΨ.1
    exact (this.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const
  have hslow : ∀ j : Fin 2, fieldCellMean (fun z => slowPartial j Ψ X z) =
      if n = 2 then fderiv ℝ f X (basisVec j) else 0 := by
    intro j
    rw [fieldCellMean_slowPartial hΨ.1 X j]
    by_cases hn2 : n = 2
    · subst hn2
      have hΨf : Ψ = fun X' _ => f X' := by
        funext X' z'
        exact hseq.1 f hf t ht X' z'
      have : (fun X' => fieldCellMean (Ψ X')) = f := by
        funext X'
        rw [hΨf]; exact fieldCellMean_const _
      rw [this]; simp
    · have hmean : ∀ X', fieldCellMean (Ψ X') = 0 := by
        intro X'
        by_cases hle : n - 2 ≤ N
        · exact liftApply_fieldCellMean_eq_zero Q sX sZ a b N H Cc hseq 0 (Nat.zero_le H)
            (n - 2) (by omega) hle f hf t ht X'
        · have : Ψ = fun _ _ => 0 := liftApply_eq_zero_of_coeff _ _
            (fun m α t X z v u => hseq.2.2.1 0 (Nat.zero_le H) (n - 2) (by omega) m α t X z v u)
            _ _
          rw [this]; exact fieldCellMean_zero
      have : (fun X' => fieldCellMean (Ψ X')) = fun _ => 0 := funext hmean
      rw [this]; simp [hn2]
  have hcA : Continuous (fun z => (Real.sqrt Q.η * Q.v t z k₀) • Φ X z) :=
    ((continuous_const.mul ((continuous_apply k₀).comp (setting_drift_continuous P t ht))).fun_smul
      hcΦ)
  have hcB : Continuous (fun z => Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k₀ j • fastPartial j Φ X z) :=
    continuous_const.fun_smul (continuous_finsetSum _ fun j _ => continuous_const.fun_smul (hcfast j))
  have hcC : Continuous (fun z => Q.η • ∑ j : Fin 2, Q.G t X k₀ j • slowPartial j Ψ X z) :=
    continuous_const.fun_smul (continuous_finsetSum _ fun j _ => continuous_const.fun_smul (hcslow j))
  have hfs := fieldCellMean_sum (Finset.univ : Finset (Fin 2))
    (f := fun j z => Q.G t X k₀ j • fastPartial j Φ X z)
    (fun j _ => continuous_const.fun_smul (hcfast j))
  have hss := fieldCellMean_sum (Finset.univ : Finset (Fin 2))
    (f := fun j z => Q.G t X k₀ j • slowPartial j Ψ X z)
    (fun j _ => continuous_const.fun_smul (hcslow j))
  have hflux : (fun z => liftFluxX Q Cc (fun _ => f) 0 n t X z k₀) = fun z =>
      ((Real.sqrt Q.η * Q.v t z k₀) • Φ X z -
        Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k₀ j • fastPartial j Φ X z) +
        -(Q.η • ∑ j : Fin 2, Q.G t X k₀ j • slowPartial j Ψ X z) := by
    funext z
    simp [liftFluxX, show 2 ≤ n by omega, hΦdef, hΨdef]
  have e1 : fieldCellMean (fun z => ((Real.sqrt Q.η * Q.v t z k₀) • Φ X z -
        Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k₀ j • fastPartial j Φ X z) +
        -(Q.η • ∑ j : Fin 2, Q.G t X k₀ j • slowPartial j Ψ X z)) =
      fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k₀) • Φ X z -
        Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k₀ j • fastPartial j Φ X z) +
      fieldCellMean (fun z => -(Q.η • ∑ j : Fin 2, Q.G t X k₀ j • slowPartial j Ψ X z)) :=
    fieldCellMean_add (hcA.sub hcB) hcC.neg
  have e2 : fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k₀) • Φ X z -
        Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k₀ j • fastPartial j Φ X z) =
      fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z k₀) • Φ X z) -
      fieldCellMean (fun z => Real.sqrt Q.η • ∑ j : Fin 2, Q.G t X k₀ j • fastPartial j Φ X z) :=
    fieldCellMean_sub hcA hcB
  rw [hflux, e1, e2, fieldCellMean_neg, fieldCellMean_smul, fieldCellMean_smul, hfs, hss]
  simp only [fieldCellMean_smul, hfast, hslow, smul_zero, Finset.sum_const_zero, sub_zero]
  rw [setting_diagonal_mean_flux_coefficient_vector_apply P sX sZ Cc hseq n hn f k₀ t ht X z]
  by_cases hn2 : n = 2
  · subst hn2
    simp only [ite_true, neg_smul]
    rfl
  · simp only [hn2, ite_false, smul_zero, Finset.sum_const_zero, neg_zero, add_zero]
    rfl

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **A periodic smooth field with prescribed jets at a point** (`IsMeanPresentation` needs
periodic fields).

`periodic_jet_realization`: a `C^K` function has, at a point `x`, the jets of orders `≤ K` of
a smooth `ℤ²`-periodic function. The function is the periodization `H (fract (y - x + c))`, `c =
(1/2, 1/2)`, of `H w = b (w + x - c) • T (w + x - c)`, where `T` is the Taylor polynomial
(`smoothJetRealization`) and `b` a bump equal to `1` near `x` supported in the sup-ball of radius
`1/4`: it vanishes unless every coordinate of `w` lies in `(1/4, 3/4)`, which makes the
periodization smooth across the cell faces.

Degenerate cases: `f` periodic and smooth (then `g` has its jets); `K = 0` (a bump times the
value). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev AVenhance Filter Topology

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Eventually equal functions have the same ordered derivatives at the point. -/
theorem orderedDerivative_congr {m : ℕ} (α : DerivativeWord2 m) {f g : Vec 2 → E}
    {x : Vec 2} (hfg : f =ᶠ[𝓝 x] g) : orderedDerivative α f x = orderedDerivative α g x := by
  have key : ∀ (l : List (Fin 2)) (f g : Vec 2 → E), f =ᶠ[𝓝 x] g →
      l.foldl (fun g' i => fun z => fderiv ℝ g' z (basisVec i)) f =ᶠ[𝓝 x]
        l.foldl (fun g' i => fun z => fderiv ℝ g' z (basisVec i)) g := by
    intro l
    induction l with
    | nil => exact fun f g h => h
    | cons i l ih =>
      intro f g h
      refine ih _ _ ?_
      filter_upwards [h.fderiv (𝕜 := ℝ)] with z hz
      exact congrArg (fun L : Vec 2 →L[ℝ] E => L (basisVec i)) hz
  exact (key _ f g hfg).self_of_nhds

open AVRegularity.Providers.GenSem

omit [NormedSpace ℝ E] in
/-- The periodization of a function supported in the open middle half-cell agrees, within `1/4`
of a point, with the shift by the floor of that point. -/
theorem periodize_eq {H : Vec 2 → E}
    (hH : ∀ w, H w ≠ 0 → ∀ i, 1 / 4 < w i ∧ w i < 3 / 4) (z0 z : Vec 2)
    (hz : ∀ i, |z i - z0 i| < 1 / 4) :
    periodize H z = H (fun i => z i - (⌊z0 i⌋ : ℤ)) := by
  unfold periodize
  by_cases hall : ∀ i, ⌊z i⌋ = ⌊z0 i⌋
  · congr 1
    funext i
    rw [Int.fract, hall i]
  · obtain ⟨i, hi⟩ := not_forall.1 hall
    have h1 := Int.floor_le (z0 i)
    have h2 := Int.lt_floor_add_one (z0 i)
    have h3 := Int.floor_le (z i)
    have h4 := Int.lt_floor_add_one (z i)
    have h5 := abs_lt.1 (hz i)
    have hne : (⌊z i⌋ : ℝ) ≠ ⌊z0 i⌋ := by exact_mod_cast hi
    have hbad : ∀ w : Vec 2, (¬ (1 / 4 < w i ∧ w i < 3 / 4)) → H w = 0 := fun w hw => by
      by_contra hne'
      exact hw (hH w hne' i)
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · have hlt' : (⌊z i⌋ : ℝ) ≤ ⌊z0 i⌋ - 1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
      rw [hbad _ (by simp only [Int.fract]; intro h; linarith [h.1])]
      rw [hbad _ (by intro h; linarith [h.1, h.2])]
    · have hgt' : (⌊z0 i⌋ : ℝ) + 1 ≤ ⌊z i⌋ := by exact_mod_cast hgt
      rw [hbad _ (by simp only [Int.fract]; intro h; linarith [h.1, h.2])]
      rw [hbad _ (by intro h; linarith [h.1, h.2])]

open AVRegularity.Construction.Preservation.Residual.FluxCancellation in
/-- **A periodic smooth function with the jets of a `C^K` function at a point.** -/
theorem periodic_jet_realization (K : ℕ) (f : Vec 2 → E) (hf : ContDiff ℝ (K : ℕ) f)
    (x : Vec 2) :
    ∃ g : Vec 2 → E, ContDiff ℝ (⊤ : ℕ∞) g ∧ IsZ2Periodic g ∧
      ∀ (r : ℕ) (I : DerivativeWord2 r), r ≤ K →
        orderedDerivative I g x = orderedDerivative I f x := by
  obtain ⟨T, hT, hTj⟩ := smoothJetRealization K f hf x
  let b : ContDiffBump x := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  let c : Vec 2 := fun _ => 1 / 2
  let sh : Vec 2 → Vec 2 := fun w => w + x - c
  have hsh : ContDiff ℝ (⊤ : ℕ∞) sh := (contDiff_id.add contDiff_const).sub contDiff_const
  let H : Vec 2 → E := fun w => b (sh w) • T (sh w)
  have hHsm : ContDiff ℝ (⊤ : ℕ∞) H :=
    (b.contDiff.comp hsh).smul (hT.comp hsh)
  have hH0 : ∀ w, H w ≠ 0 → ∀ i, 1 / 4 < w i ∧ w i < 3 / 4 := by
    intro w hw i
    have hb : b (sh w) ≠ 0 := fun h0 => hw (by simp [H, h0])
    have hmem : sh w ∈ Metric.ball x (1 / 4) := by
      rw [← b.support_eq]
      exact hb
    have h1 := (dist_pi_lt_iff (by norm_num : (0 : ℝ) < 1 / 4)).1 hmem i
    rw [Real.dist_eq] at h1
    have h2 := abs_lt.1 h1
    simp only [sh, c, Pi.add_apply, Pi.sub_apply] at h2
    constructor <;> linarith [h2.1, h2.2]
  let zf : Vec 2 → Vec 2 := fun y => y - x + c
  let g : Vec 2 → E := fun y => periodize H (zf y)
  have hzf : ContDiff ℝ (⊤ : ℕ∞) zf := (contDiff_id.sub contDiff_const).add contDiff_const
  have hsm : ContDiff ℝ (⊤ : ℕ∞) g := by
    rw [contDiff_iff_contDiffAt]
    intro y0
    let N0 : Vec 2 := fun i => ((⌊zf y0 i⌋ : ℤ) : ℝ)
    have hev : g =ᶠ[𝓝 y0] fun y => H (zf y - N0) := by
      filter_upwards [Metric.ball_mem_nhds y0 (by norm_num : (0 : ℝ) < 1 / 4)] with y hy
      refine periodize_eq hH0 (zf y0) (zf y) fun i => ?_
      have := (dist_pi_lt_iff (by norm_num : (0 : ℝ) < 1 / 4)).1 hy i
      rw [Real.dist_eq] at this
      simpa [zf] using this
    exact ((hHsm.contDiffAt.comp y0
      ((hzf.sub contDiff_const).contDiffAt))).congr_of_eventuallyEq hev
  have hper : IsZ2Periodic g := by
    intro n y
    have : zf (y + latticeShift n) = zf y + latticeShift n := by
      funext i
      simp only [zf, Pi.add_apply, Pi.sub_apply]
      ring
    show periodize H (zf (y + latticeShift n)) = periodize H (zf y)
    rw [this]
    exact periodize_periodic H n (zf y)
  refine ⟨g, hsm, hper, fun r I hr => ?_⟩
  have hev : g =ᶠ[𝓝 x] T := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 8)] with y hy
    have hz : periodize H (zf y) = H (zf y - fun _ => (((⌊(1 / 2 : ℝ)⌋ : ℤ)) : ℝ)) := by
      refine periodize_eq hH0 (fun _ => 1 / 2) (zf y) fun i => ?_
      have := (dist_pi_lt_iff (by norm_num : (0 : ℝ) < 1 / 8)).1 hy i
      rw [Real.dist_eq] at this
      have h2 := abs_lt.1 this
      rw [abs_lt]
      simp only [zf, c, Pi.add_apply, Pi.sub_apply]
      constructor <;> linarith [h2.1, h2.2]
    have hyb : b y = 1 := b.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall]; exact hy.le)
    have hsy : sh (zf y - fun _ => (((⌊(1 / 2 : ℝ)⌋ : ℤ)) : ℝ)) = y := by
      funext i
      have hfl : ⌊(2⁻¹ : ℝ)⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨by norm_num, by norm_num⟩
      simp [sh, zf, c, hfl]
      ring
    show periodize H (zf y) = T y
    rw [hz]
    simp only [H, hsy, hyb, one_smul]
  rw [orderedDerivative_congr I hev]
  exact hTj r I hr

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Macro swap, step (ii): jet locality of the glued mean flux, without a `SplitInput`**.

A version of `menuMeanFluxJet_of_pulse` for a general
`(rs, ns)` with the stage facts as hypotheses, as `covTruncReg_gluedMeanFlux_contDiff` is a
copy of `menuGluedMeanFlux_contDiff`: if two fields `C^{s + D_m + N}` at time `t` have the same
jets of that order at `x`, the glued mean fluxes are `C^s` and have the same `s`-jet at `x`.

Degenerate cases: `a₁ = a₂` (trivial); `rs = ∅` (both sides vanish). -/

@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.Construction.Residual.Presentation

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] in
/-- **Jet locality of the glued mean flux** (the stage facts as hypotheses). -/
theorem gluedMeanFlux_triple (Mn : SuccMenu)
    (G : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hbase : 1 ≤ D.Λ) (hprof : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hord : 1 ≤ Dm)
    (hlift : ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D G.level k (nativeChain G.level k)
          (Mn.lenFactor * liftLength D G.level)
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
        Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N depth
        (CcT k))
    (s : ℕ) (hsX : s + Dm ≤ Mn.sX) (hsZ : s + Dm ≤ Mn.sZ)
    (rs ns : Finset ℕ) (hrs : ∀ r ∈ rs, r ≤ depth)
    (hE : (∃ r ∈ rs, r ≠ 0) → ActualFluxJointSmooth G)
    (a₁ a₂ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (x : Vec 2)
    (h₁ : ContDiff ℝ ((s + Dm + Mn.N : ℕ) : ℕ∞) (a₁ t))
    (h₂ : ContDiff ℝ ((s + Dm + Mn.N : ℕ) : ℕ∞) (a₂ t))
    (hj : SameJetAt (s + Dm + Mn.N) x (a₁ t) (a₂ t)) (v : CompIn G.comps) :
    Triple s x (fun y => menuGluedMeanFlux Mn G G.level rs ns CcT a₁ t y v)
      (fun y => menuGluedMeanFlux Mn G G.level rs ns CcT a₂ t y v) := by
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hbase hprof hband G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hbase
  unfold menuGluedMeanFlux
  refine triple_sum _ fun k _ => triple_sum _ fun r hrr => triple_sum _
    fun n _ => ?_
  by_cases hodd : Odd k
  · simp only [hodd, dite_true]
    by_cases hcut : ocCutoff D.α D.q D.Λ G.level k t = 0
    · simp only [hcut, zero_smul]
      exact ⟨contDiff_const, contDiff_const, fun _ _ _ => rfl⟩
    · refine triple_smul _ ?_
      have ht' := clock_mem_window D G.level k t hτ hcc hcut
      have hwin := AVRegularity.Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
      obtain ⟨_, _, hz3, _, _, hbox, _⟩ := hlift k hodd
      refine pulse_sameJet _ _ _ n r _ _ _ _ a₁ a₂ t v s Mn.N depth x hcc.ne'
        hord (hrs r hrr) hz3 ?_ ?_ ?_ ?_ h₁ h₂ hj ?_ ?_ ?_
      · exact fun hh' hH n' m α v u => (hbox hh' hH n' m α v u _ ht').1.mono hsX hsZ
      · intro k' j
        exact (EntryWeakProofs.familyLiftData_metric_entry_smooth D G.level k _
          (by simp [nativeChain]) _ _ _ k' j).of_le (by exact_mod_cast le_top)
      · intro k'
        exact (ocPulseCellDrift_contDiff D.α D.q D.Λ D.ζ G.level (D.kap G.level) hodd _
          k').of_le (by exact_mod_cast le_top)
      · intro hr0
        exact fiber_edge_boxSmooth G (hE ⟨r, hrr, hr0⟩) k hodd _ _ t hcc.ne' hwin s
      · exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) t
          (D.slotAnchor G.level k)).of_le (by exact_mod_cast le_top)
      · exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
          (D.slotAnchor G.level k) t).of_le (by exact_mod_cast le_top)
      · exact flow_chart_label D (G.level - 1) (D.slotAnchor G.level k) t x
  · simp only [hodd, dite_false]
    exact ⟨contDiff_const, contDiff_const, fun _ _ _ => rfl⟩

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] in
/-- **Jet locality of the glued mean flux at the level `m = G.level`.** -/
theorem gluedMeanFlux_triple_m (Mn : SuccMenu)
    (G : GenStage D hr Dm b j₀) (m depth : ℕ) (hm : G.level = m)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hbase : 1 ≤ D.Λ) (hprof : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hord : 1 ≤ Dm)
    (hlift : ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D m k (nativeChain m k)
          (Mn.lenFactor * liftLength D m)
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
        Mn.sX Mn.sZ (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) Mn.N depth
        (CcT k))
    (s : ℕ) (hsX : s + Dm ≤ Mn.sX) (hsZ : s + Dm ≤ Mn.sZ)
    (rs ns : Finset ℕ) (hrs : ∀ r ∈ rs, r ≤ depth)
    (hE : (∃ r ∈ rs, r ≠ 0) → ActualFluxJointSmooth G)
    (a₁ a₂ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (x : Vec 2)
    (h₁ : ContDiff ℝ ((s + Dm + Mn.N : ℕ) : ℕ∞) (a₁ t))
    (h₂ : ContDiff ℝ ((s + Dm + Mn.N : ℕ) : ℕ∞) (a₂ t))
    (hj : SameJetAt (s + Dm + Mn.N) x (a₁ t) (a₂ t)) (v : CompIn G.comps) :
    Triple s x (fun y => menuGluedMeanFlux Mn G m rs ns CcT a₁ t y v)
      (fun y => menuGluedMeanFlux Mn G m rs ns CcT a₂ t y v) := by
  subst hm
  exact gluedMeanFlux_triple Mn G depth CcT hbase hprof hband hord hlift s hsX hsZ rs ns hrs
    hE a₁ a₂ t x h₁ h₂ hj v

end AVRegularity.Construction.Residual.Presentation
end
end
end

section
section
/-! **The premises of the core and the tail** (glued mean, step (i)).

`ReconGluedMeanCore` and `ReconGradeZeroTail` speak about `c.CcT`, which is
only an existential witness of `IsTerminalLiftedField`; the lift-sequence properties of the window
(`IsLiftSequence`: `C_n = 0` for `n > N_T`, cell-mean-zero of the lifts, box smoothness) and the
regularity of the settings hold only through the lift sequence (`ReconSeqAt`, `reconSeqStep_of_ctx`) and the lift setting
(`ReconSettingAt`), at an offset `ℓ` supplied by the prefix. The two lemmas below carry these two
premises; `reconGluedMeanFix_of_core` assembles `ReconGluedMeanAt` from them. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.CycleComparison.Coarse

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

section GluedCoreFix

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- **The core of (i), with the lift sequence and lift setting premises.** -/
def ReconGluedMeanCoreFix (x : TermResAux c) (ℓ : ℕ) (CGl Cw' : ℕ → ℝ) (Ca Sb Cg : ℝ)
    (r : ℕ) : Prop :=
  ReconSeqAt c ℓ → ReconSettingAt c x ℓ CGl Cw' Ca Sb Cg → ReconGluedMeanCore c r

/-- **The grade-zero tail, with the lift sequence and lift setting premises.** -/
def ReconGradeZeroTailFix (x : TermResAux c) (ℓ : ℕ) (CGl Cw' : ℕ → ℝ) (Ca Sb Cg : ℝ) :
    Prop :=
  ReconSeqAt c ℓ → ReconSettingAt c x ℓ CGl Cw' Ca Sb Cg → ReconGradeZeroTail c

end GluedCoreFix

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Step (iii) of the conversion: the split of the mean flux and the realizations.** At a time of the
window the mean flux `F_mean` of the menu is `F_cov - F_filter - F_front` (`menuMeanFluxSplit`), and
the realizations `F1, F2, F3` are those three fluxes almost everywhere on the cell, so the torus
jet of `F_c = F1 - F3 - F2` is `F_mean` almost everywhere (`jet_sub_ae`).

Degenerate cases:
- `p_T = 0`: the split is the definition of `menuMeanFluxF`.
- `F1 = F2 = F3 = 0`: all three fluxes vanish almost everywhere, so does `F_mean`. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.CycleComparison.Coarse

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **Step (iii) at every context.** -/
theorem reconMeanFluxAt_of_ctx
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc : ℕ)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    ReconMeanFluxAt c x kc F1 F2 F3 := by
  intro hreal hsm v t ht
  obtain ⟨h1, h2, h3⟩ := hreal
  have e1 := h1 v t ht
  have e2 := h2 v t ht
  have e3 := h3 v t ht
  filter_upwards [jet_sub_ae (F1 v t - F3 v t) (F2 v t), jet_sub_ae (F1 v t) (F3 v t), e1, e2, e3]
    with y hs1 hs2 a1 a2 a3
  have hs := menuMeanFluxSplit (Mn := A.Mt M sXT sZT c.tp cr) (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW)
    (A.Kn_ c.D M cr) A.φ₀ c.Gw c.Gt' (c.Gt'.retained M 1 A.RT) M A.NT A.pT A.dW 1 A.RT
    (c.D.eps (M - 1)) A.η₀ c.CcT x.aZ x.aY v t (hsm v t ht).1 (hsm v t ht).2 y
  change (F1 v t - F3 v t - F2 v t).toFunction.jet (valueIndex2 kc) y = _
  rw [hs1, hs2, a1, a2, a3, hs]
  simp [toFluxL, WithLp.toLp_sub]

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Step (iv) of the conversion: `ReconDensityAt`**. The generic theorem
`CoarseDefectOfSmooth` applied to the window: the retained field is bounded by continuity on
the compact window, `F_c = F₁ - F₃ - F₂` has `‖F_c s‖` integrable by square integrability. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.CycleComparison.Coarse

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

theorem tp_add_rTobs : c.tp + rTobs c = c.a + A.T₀ := by
  simp [rTobs]

/-- The retained field of the window is bounded (continuity on the compact window). -/
theorem reconW_bounded (kc : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (hcont : ∀ v, ContinuousOn (reconW c kc hW v) (Set.Icc c.tp (c.a + A.T₀))) :
    ∃ MW : ℝ, ∀ s ∈ Set.Icc c.tp (c.a + A.T₀), ∀ v, ‖reconW c kc hW v s‖ ≤ MW := by
  have h1 : ∀ v, ∃ Mv : ℝ, ∀ s ∈ Set.Icc c.tp (c.a + A.T₀), ‖reconW c kc hW v s‖ ≤ Mv :=
    fun v => isCompact_Icc.exists_bound_of_continuousOn (hcont v)
  choose Mv hMv using h1
  refine ⟨∑ v, |Mv v|, fun s hs v => ?_⟩
  exact (hMv v s hs).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun v => |Mv v|) (fun v _ => abs_nonneg _) (Finset.mem_univ v)))

/-- `‖F_c s‖` is integrable on the window. -/
theorem reconFc_norm_integrable (kc : ℕ)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (v : CompIn c.Gw.comps)
    (h1 : MemLp (F1 v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀))))
    (h2 : MemLp (F2 v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀))))
    (h3 : MemLp (F3 v) 2 (volume.restrict (Set.Icc c.tp (c.a + A.T₀)))) :
    IntegrableOn (fun s => ‖reconFc c F1 F2 F3 v s‖) (Set.Icc c.tp (c.a + A.T₀)) := by
  have i1 := (h1.integrable one_le_two).norm
  have i2 := (h2.integrable one_le_two).norm
  have i3 := (h3.integrable one_le_two).norm
  have hm : AEStronglyMeasurable (fun s => reconFc c F1 F2 F3 v s)
      (volume.restrict (Set.Icc c.tp (c.a + A.T₀))) :=
    (h1.aestronglyMeasurable.sub h3.aestronglyMeasurable).sub h2.aestronglyMeasurable
  refine Integrable.mono' ((i1.add i3).add i2) hm.norm (Filter.Eventually.of_forall fun s => ?_)
  simp only [reconFc, Real.norm_eq_abs, abs_norm, Pi.add_apply]
  exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)

/-- **(iv) Density**, proved. -/
theorem reconDensityAt_proof (kc : ℕ) (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT)
    (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    ReconDensityAt c kc hW hf F1 F2 F3 := by
  intro hTR aC B₀C lamC AD CE Aedge Cstar Θc hlet hsm
  obtain ⟨P, -⟩ := hlet
  obtain ⟨hF1, hF2, hF3, hcont⟩ := hTR
  have hwin := tp_add_rTobs c
  obtain ⟨MW, hMW⟩ := reconW_bounded c kc hW hcont
  have hFc : ∀ v, IntegrableOn (fun s => ‖reconFc c F1 F2 F3 v s‖)
      (Set.Icc c.tp (c.tp + rTobs c)) := fun v => by
    rw [hwin]; exact reconFc_norm_integrable c kc F1 F2 F3 v (hF1 v) (hF2 v) (hF3 v)
  rw [← hwin] at hMW
  exact CoarseDefectOfSmooth P hMW hFc hsm

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **Step (vi): `ReconTransferAt`**. The coarse equation, rewritten by
the jets (v), the swap (ii) and the mean flux (iii), is the smooth-test defect of `reconW`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.CycleComparison.Coarse

namespace AVRegularity.EntryTerminal.Ingredients.Recon

section Jets

variable {K : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A classical representative has the value jet as its value, almost everywhere on the cell. -/
theorem tval_ae' {W : TorusHk K E} {a : Vec 2 → E} {r : ℕ} (h : IsClassicalRep W a r) :
    tval W =ᵐ[volume.restrict unitCube] a := by
  filter_upwards [h.2.2.2 0 (Nat.zero_le _) Fin.elim0] with x hx
  have h1 : torusJetOrder W 0 Fin.elim0 x = tval W x := by
    simp [torusJetOrder, tval, valueIndex2, valueIndex]
  have h2 : orderedDerivative (Fin.elim0 : DerivativeWord2 0) a x = a x := by
    simp [orderedDerivative]
  rw [← h1, hx, h2]

/-- A classical representative of order `≥ 1` has the first jets as its gradient, almost
everywhere on the cell. -/
theorem grad_ae {W : TorusHk K E} {a : Vec 2 → E} {r : ℕ} (h : IsClassicalRep W a r)
    (hr : 1 ≤ r) :
    ∀ᵐ x ∂(volume.restrict unitCube), ∀ k : Fin 2,
      gradE a x k = torusJetOrder W 1 (fun _ => k) x := by
  rw [ae_all_iff]
  intro k
  filter_upwards [h.2.2.2 1 hr (fun _ => k)] with x hx
  rw [hx]
  rfl

end Jets

section Main

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

variable (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
  Ce cker j₀ M)

/-- **(vi) The transfer**, proved. -/
theorem reconTransferAt_proof (x : TermResAux c) (kc : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) :
    ReconTransferAt c x kc hW hf F1 F2 F3 := by
  intro aC B₀C lamC AD CE Aedge Cstar Θc hlet hweak hjets hswap hmean v t ht ψ hψ hp
  obtain ⟨P, -⟩ := hlet
  have hwin := tp_add_rTobs c
  have htw : t ∈ Set.Icc c.tp (c.a + A.T₀) := by rw [← hwin]; exact ht
  have hr1 : 1 ≤ A.NT + A.Dt := by have := P.D_ge; omega
  obtain ⟨-, -, hI3, hI4, hid⟩ := hweak v t htw ψ hψ hp
  have key : ∀ s ∈ Set.Ioc c.tp t, _ := fun s hs => by
    have hsw : s ∈ Set.Icc c.tp (c.a + A.T₀) := ⟨hs.1.le, hs.2.trans htw.2⟩
    have hsw' : s ∈ Set.Icc c.tp (c.tp + rTobs c) := by rw [hwin]; exact hsw
    obtain ⟨hPm, hPc, hint⟩ := hswap v s hsw' ψ hψ hp
    have hdu := grad_ae (hjets.1 v s hsw) hr1
    have hF := hmean v s hsw
    exact TransferPoint (μ := volume.restrict unitCube) (c.D.κ (M - 1))
      (streamVel (c.D.Φ (M - 1)) s) ψ (fun k y => gradE ψ y k)
      (fun k y => gradE (fun y' => c.aRep s y' v) y k)
      (fun k y => torusJetOrder (reconW c kc hW v s) 1 (fun _ => k) y) _ _ _ _ hdu hF
      (hI3 s hs) hPm hPc hint
  have hct : cellInner (tval (reconW c kc hW v t)) ψ =
      ∫ y in unitCube, inner ℝ (c.aRep t y v) (ψ y) := by
    refine integral_congr_ae ?_
    filter_upwards [tval_ae' (hjets.1 v t htw)] with y hy
    rw [hy]
  have hc0 : cellInner (fun y => (truncateTorusHk hf (c.PZ v c.tp)).toFunction.jet
      (valueIndex2 (rNc A kc)) y) ψ = ∫ y in unitCube, inner ℝ (c.aRep c.tp y v) (ψ y) := by
    refine integral_congr_ae ?_
    filter_upwards [tval_ae' (hjets.2 (htw.1.trans htw.2) v)] with y hy
    exact congrArg (fun z => inner ℝ z (ψ y)) hy
  refine ⟨hI4.congr_fun (fun s hs => ((key s hs).2).symm) measurableSet_Ioc, ?_⟩
  rw [hct, hc0]
  refine hid.trans ?_
  exact (setIntegral_congr_fun measurableSet_Ioc (fun s hs => (key s hs).2)).symm

end Main

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
/-! **The conversion to the coarse defect with steps (iii)-(vi) discharged**. Only the glued mean (i) and the
macro swap (ii) remain as hypotheses. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction
open AVRegularity.CycleComparison.Coarse

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **The conversion (plus) at a context from the glued mean (i) and the macro swap (ii) alone.** -/
theorem reconDefectConvPlusAt_of_glued_swap
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc ℓ : ℕ)
    (hW : kc + 1 + (A.NT + A.Dt) ≤ A.Khat Kout - 2 * A.pT) (hf : rNc A kc ≤ A.Khat Kout - 2 * A.pT)
    (F1 F2 F3 : ∀ v : CompIn c.Gw.comps, ℝ → TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (hG : ∀ r ∈ Finset.range (A.dW + 1), ReconGluedMeanAt c r) (hS : ReconMacroSwapAt c kc hW hf) :
    ReconDefectConvPlusAt c x kc ℓ hW hf F1 F2 F3 :=
  reconDefectConvPlusAt_of_steps c x kc ℓ hW hf F1 F2 F3
    ⟨reconJetsAt_of_ctx c kc hW hf, hG, hS, reconMeanFluxAt_of_ctx c x kc F1 F2 F3,
      reconTransferAt_proof c x kc hW hf F1 F2 F3, reconDensityAt_proof c kc hW hf F1 F2 F3⟩

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end
