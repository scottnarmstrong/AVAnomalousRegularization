-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FineDefectTime
import AVRegularity.CycleComparison.Lift.SettingSourceLiftConvolutionAllDegrees
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FluxBoundBasic
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
import AVenhance.Infra.Construction.StreamAdmissible

section
section
/-! Diagonal and mean bounds from their exact operators on gradient carriers.

Each operator has price C B, B=κ(M-1), at order kc+4pT. The higher gradient realization
has mass C ||f||/B by the already proved strong-energy bound, so their composition costs
C² ||f||. All floors and constants precede j0, M, the phase, components and datum.

Hypotheses: CovTruncDiagOperatorStatement and CovTruncMeanOperatorStatement. These
ask for the actual flux operator, its measurable action and its mass-weighted bound; an
operator with only the correct divergence does not satisfy their realization clause.
Route: lift sequences and lift settings at the higher offset through ReconPrefixU; diagonal/positive mean coefficients
and zero tested-order support; physical chart transfer; Sobolev coefficient multiplication,
finite weighted Schur sums and gluing. No new cell existence or energy estimate is needed.

Special cases: EMPTY components give zero operators and zero mass; one component reduces the
Schur bound to its scalar version; zero datum costs zero; dW=0 has zero mean operator; the
second diagonal degree includes the molecular metric flux; a point window has zero integral.
The choice cr=1 is supplied by TermResAux, not inserted into either statement. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.EntryTerminal.CovGrad

namespace AVRegularity.Construction.Residual.Presentation

/-- Input gradient order paying for the covariance polynomial, cell degree and output jets. -/
def covTruncMeanInputOrder {X : TermConstruction} (A : TermArgs X) (kc : ℕ) : ℕ :=
  kc + 6 * A.pT + A.NT + A.Dt

section Context
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- The gradient realization at the higher input order, with its inverse-diffusivity price. -/
def CovTruncMeanGradientAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  HasFluxBound (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root)
    (covTruncMeanInputOrder A kc) (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1))
    (c.D.termRho cr M) (c.Gw.mass c.lawW)
    (fun v t y => toFluxL (gradE (fun z => x.aZ t z v) y))
    (C * c.normF / c.D.κ (M - 1))

/-- The classical flux selected by the diagonal/positive split. -/
def covTruncMeanTarget (diagonal : Bool) (x : TermResAux c) (v : CompIn c.Gw.comps)
    (t : ℝ) (y : Vec 2) : PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root) :=
  toFluxL (if diagonal then
    gDiagTerm (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT c.CcT x.aZ v t y else
    gMeanTerm (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t y)

/-- Exact, measurable action with price C B on the finite family of input gradient carriers. -/
def CovTruncMeanOperatorAt (diagonal : Bool) (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  Nonempty (CovTruncFluxOperator (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root)
    (covTruncMeanInputOrder A kc) (kc + 4 * A.pT) (Set.Icc c.tp (c.a + A.T₀))
    (c.D.termRho cr M) (c.Gw.mass c.lawW) (C * c.D.κ (M - 1))
    (fun v t y => toFluxL (gradE (fun z => x.aZ t z v) y))
    (covTruncMeanTarget c diagonal x))
/-- The selected flux bound at its output order. -/
def CovTruncMeanBoundAt (diagonal : Bool) (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  HasFluxBound (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root) (kc + 4 * A.pT)
    (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M)
    (c.Gw.mass c.lawW) (covTruncMeanTarget c diagonal x) (C * c.normF)
end Context

/-- The actual positive-grade glued mean flux operator. -/
def CovTruncMeanOperatorStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => CovTruncMeanOperatorAt c false x kc C

/-- The already proved strong energy supplies the required higher-order gradient input. -/
theorem covTruncMeanGradient :
    TermResPrefix fun c x kc _ C _ _ => CovTruncMeanGradientAt c x kc C := by
  intro X
  obtain ⟨Λ₀, h128, henergy⟩ := covGrad_ctx_energy X
  refine ⟨Λ₀, h128, fun A hΛ hV => ⟨0, fun kc _ =>
    ⟨0, 0, covTruncMeanInputOrder A kc + 3, fun sXT sZT _ _ Kout hK => ⟨0, ?_⟩⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker _ Cfl
  let Cgrad := Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) *
    (Real.sqrt 2 * max CP 0)
  refine ⟨Cgrad, 1, 1, one_pos, 1, 1, le_rfl, one_pos, fun C hC j₀ _ => ?_⟩
  obtain ⟨M₀, hE⟩ := henergy A hΛ hV cHP
  refine ⟨max M₀ 2, fun M hM c x => ?_⟩
  have horder : kc + 4 * A.pT + A.NT + A.Dt + 2 * A.pT + 3 ≤ A.Khat Kout := by
    have h : Kout ≤ A.Khat Kout := le_max_left _ _
    dsimp [covTruncMeanInputOrder] at hK
    omega
  have hf := hE (le_trans (le_max_left _ _) hM) c x
    (kc + 4 * A.pT + A.NT + A.Dt) horder
  have hν : 0 < c.D.κ (M - 1) :=
    CycleReference.bandChain_pos (by omega : 1 ≤ A.Λ) X.hζ c.data.2.2.2.2.2.1
      (Nat.sub_le M 1)
  have hmass :
      (Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) *
        (Real.sqrt 2 * max CP 0 * c.normF)) / c.D.κ (M - 1) ≤
          C * c.normF / c.D.κ (M - 1) := by
    apply div_le_div_of_nonneg_right _ hν.le
    calc
      _ = Cgrad * c.normF := by dsimp [Cgrad]; ring
      _ ≤ C * c.normF := mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _)

  have heq : kc + 4 * A.pT + A.NT + A.Dt + 2 * A.pT = covTruncMeanInputOrder A kc := by
    dsimp [covTruncMeanInputOrder]; omega
  rw [heq] at hf
  exact hasFluxBound_mono_Y hf hmass

/-- Uniform exact operator action plus strong energy gives either part of the mean-flux bound. -/
theorem covTruncMeanBound_of_operator (diagonal : Bool)
    (hOp : TermResPrefix fun c x kc _ C _ _ => CovTruncMeanOperatorAt c diagonal x kc C) :
    TermResPrefix fun c x kc _ C _ _ => CovTruncMeanBoundAt c diagonal x kc C := by
  have hjoin := termFluxPrefix_and
    (P₁ := fun c x kc C => CovTruncMeanOperatorAt c diagonal x kc C)
    (P₂ := fun c x kc C => CovTruncMeanGradientAt c x kc C) hOp covTruncMeanGradient
  refine termFluxPrefix_map (P := fun c x kc C =>
    CovTruncMeanOperatorAt c diagonal x kc C ∧ CovTruncMeanGradientAt c x kc C) ?_ hjoin
  intro X A kc C₁ hΛ hC₁
  refine ⟨C₁ ^ 2, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hP C' hC'
  obtain ⟨⟨P⟩, hgrad⟩ := hP
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos (by omega) X.hζ
    c.data.2.2.2.2.2.1 (Nat.sub_le M 1)
  have hq : 1 < c.D.q := c.data.2.1 ▸ X.hq.1
  have hΛD : 128 ≤ c.D.Λ := c.data.2.2.1 ▸ hΛ
  have hπ : ∀ v, 0 < c.Gw.mass c.lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq hΛD c.lawW v.1
  have hf := P.hasFluxBound measurableSet_Icc hν hπ (mul_nonneg hC₁ hν.le) hgrad
  have hcost : (C₁ * c.D.κ (M - 1)) * (C₁ * c.normF / c.D.κ (M - 1)) =
      C₁ ^ 2 * c.normF := by field_simp [hν.ne']
  rw [hcost] at hf
  exact hasFluxBound_mono_Y hf (mul_le_mul_of_nonneg_right hC' (Real.sqrt_nonneg _))

/-- Exact mean statement, with the strong-energy ingredient discharged. -/
theorem covTruncMean_of_operator (hOp : CovTruncMeanOperatorStatement) :
    CovTruncMeanStatement := covTruncMeanBound_of_operator false hOp

end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! **The covariance truncation with every step proved except `CovTruncGStatement`**.

`termCovTrunc_of_G` is `termCovTrunc_of_steps` with the operator step `covTruncOp`, the difference
step `covTruncSub`, the size step `covTruncSize` and the gradient step `covTruncGradStep` supplied;
the one remaining hypothesis is `CovTruncGStatement`. -/

@[expose] public section

namespace AVRegularity.Construction.Residual.Presentation

/-- **The covariance truncation from `CovTruncGStatement` alone.** -/
theorem termCovTrunc_of_G (hG : CovTruncGStatement) : TermCovTruncStatement :=
  termCovTrunc_of_steps covTruncOp covTruncSub covTruncSize hG covTruncGradStep

end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! The actual slow-flux cell mean is the differential action of its explicit mean
coefficients. This identifies the flux itself, including the molecular term at diagonal
degree two, rather than replacing it by a flux with the same divergence.

These are the smooth-input identities for the operator ingredients of the cell-mean operator. Their finite
regularity extension uses the existing smooth-jet realization and finite-jet locality.
Special cases: grade zero has no source; positive grade has a centered degree-zero predecessor;
only diagonal degree two contributes the molecular metric term; coefficients above the
cutoff give zero lift fields. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity
open AVRegularity.CycleComparison.Lift

namespace AVRegularity.Construction.Residual.Presentation

private theorem covTruncCellMean_cross {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (η : ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (v : Vec 2 → Vec 2)
    (Φ Ψ : Vec 2 → Vec 2 → E) (hΦ : GoodField 1 Φ) (hΨ : GoodField 1 Ψ)
    (hv : Continuous v) (X : Vec 2) (k : Fin 2) :
    fieldCellMean (fun z =>
      ((Real.sqrt η * v z k) • Φ X z -
        Real.sqrt η • ∑ j : Fin 2, G X k j • fastPartial j Φ X z) -
        η • ∑ j : Fin 2, G X k j • slowPartial j Ψ X z) =
      fieldCellMean (fun z => (Real.sqrt η * v z k) • Φ X z) -
        η • ∑ j : Fin 2, G X k j •
          fderiv ℝ (fun Y => fieldCellMean (Ψ Y)) X (basisVec j) := by
  have hD : Continuous (fun z => (Real.sqrt η * v z k) • Φ X z) :=
    (continuous_const.mul ((continuous_apply k).comp hv)).smul (hΦ.continuous_slice X)
  have hF : Continuous (fun z => Real.sqrt η •
      ∑ j : Fin 2, G X k j • fastPartial j Φ X z) :=
    (continuous_finsetSum _ fun j _ =>
      ((hΦ.fastPartial j).continuous_slice X).const_smul (G X k j)).const_smul _
  have hS : Continuous (fun z => η • ∑ j : Fin 2, G X k j • slowPartial j Ψ X z) :=
    (continuous_finsetSum _ fun j _ =>
      ((hΨ.slowPartial j).continuous_slice X).const_smul (G X k j)).const_smul _
  have hf0 : fieldCellMean (fun z => Real.sqrt η •
      ∑ j : Fin 2, G X k j • fastPartial j Φ X z) = 0 := by
    rw [fieldCellMean_smul, fieldCellMean_sum Finset.univ (f := fun j z => G X k j • fastPartial j Φ X z) (fun j _ =>
      ((hΦ.fastPartial j).continuous_slice X).const_smul (G X k j))]
    simp only [fieldCellMean_smul]
    have hz : ∀ j, fieldCellMean (fun z => fastPartial j Φ X z) = 0 :=
      fun j => (GoodField.cent_fastPartial (c := True) hΦ j).2 trivial X
    simp only [hz, smul_zero, Finset.sum_const_zero]
  let d := fun z => (Real.sqrt η * v z k) • Φ X z
  let f := fun z => Real.sqrt η • ∑ j : Fin 2, G X k j • fastPartial j Φ X z
  let s := fun z => η • ∑ j : Fin 2, G X k j • slowPartial j Ψ X z
  change fieldCellMean ((d - f) - s) = _
  calc
    _ = fieldCellMean (d - f) - fieldCellMean s := fieldCellMean_sub (hD.sub hF) hS
    _ = (fieldCellMean d - fieldCellMean f) - fieldCellMean s :=
      congrArg (fun y => y - fieldCellMean s) (fieldCellMean_sub hD hF)
    _ = _ := by
      rw [hf0, sub_zero]
      dsimp [d, s]
      rw [fieldCellMean_smul, fieldCellMean_sum Finset.univ (f := fun j z => G X k j • slowPartial j Ψ X z) (fun j _ =>
        ((hΨ.slowPartial j).continuous_slice X).const_smul (G X k j))]
      simp only [fieldCellMean_smul, fieldCellMean_slowPartial hΨ.1 X]

section Setting
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- The positive-grade actual mean flux is the action of the explicit positive coefficients. -/
theorem covTruncCellMean_positive (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (hh n : ℕ)
    (hhpos : 1 ≤ hh) (hhh : hh ≤ H) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) (j : Fin 2) :
    fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) hh n t X z j) =
      liftApply (n - 1) (positiveMeanFluxCoefficient Q Cc hh n j) (fun _ => f) t X 0 := by
  have hΦ := liftApply_goodField_of_seq Q hseq (by omega : 1 ≤ sX) (by omega : 1 ≤ sZ)
    hhh (n - 1) hf ht
  have hΨ := liftApply_centField_of_seq Q hseq (by omega : 1 ≤ sX) (by omega : 1 ≤ sZ)
    hhh (Or.inr hhpos) hf ht (n := n - 2)
  have hgood := fun q => setting_liftApply_goodField_D_all P sX sZ (by omega) Cc hseq
    (hh - 1) (by omega) q f hf t ht
  have hΓ : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      GoodField 1 (fun Y z => γ.coeff α t Y z) := fun v u d γ hγ α =>
    ⟨(P.coeff_smooth v u d γ hγ α t ht).contDiff_uncurry
      (setting_source_slow_reserve P) (by have := setting_source_fast_reserve P; have := P.D_ge; omega),
      γ.periodic α t⟩
  have hv : Continuous (Q.v t) := by
    have he : Q.v t = fun z => V t (z par.rev) • basisVec par := funext (P.v_shear t)
    rw [he]
    exact ((P.V_smooth t ht).continuous.comp (continuous_apply _)).smul continuous_const
  have hact := EntryWeakProofs.liftFluxX_cell_mean_intrinsic Q (by have := P.D_ge; omega)
    Cc hh n hn (by omega) (fun _ => f) t X j
    (fun i l => (P.G_smooth t ht i l).of_le (by simp))
    hv hΦ hΨ hgood hΓ
  have hconv : sourceFluxCoeff Q.edge Q.η (n - 1) t
      (fun ε => liftPolyField Cc N ε (hh - 1) (fun _ => f) t) j X =
      fun z => ∑ l ∈ Finset.range (min (D - 1) (n - 1) + 1),
        sourceFluxCoefficientArray Q.edge Q.η t
          (liftApply (n - 1 - l) (Cc (hh - 1) (n - 1 - l)) (fun _ => f) t) j l X z := by
    funext z
    exact setting_sourceFlux_lift_convolution P sX sZ (by omega) Cc hseq
      (hh - 1) (by omega) (n - 1) j f hf t ht X z
  rw [← hconv] at hact
  exact hact.trans (setting_positive_mean_flux_coefficient_vector_apply P sX sZ hsX hsZ
    Cc hseq P₀ hreserve hh hhpos hhh n hn hnR f hf j t ht X 0).symm

include P in
omit [∀ i, BorelSpace (h i)] [∀ i, MeasurableSpace (h i)] in
/-- The diagonal actual mean flux is the explicit diagonal coefficient action. The metric
term survives exactly at degree two, where the predecessor is the identity lift. -/
theorem covTruncCellMean_diagonal (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (n : ℕ) (hn : 2 ≤ n) (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) (j : Fin 2) :
    fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) 0 n t X z j) =
      liftApply (n - 1) (diagonalMeanFluxCoefficient Q Cc n j) (fun _ => f) t X 0 := by
  let Φ := liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t
  let Ψ := liftApply (n - 2) (Cc 0 (n - 2)) (fun _ => f) t
  have hΦ : GoodField 1 Φ := liftApply_goodField_of_seq Q hseq
    (by omega : 1 ≤ sX) (by omega : 1 ≤ sZ) (Nat.zero_le H) (n - 1) hf ht
  have hΨ : GoodField 1 Ψ := liftApply_goodField_of_seq Q hseq
    (by omega : 1 ≤ sX) (by omega : 1 ≤ sZ) (Nat.zero_le H) (n - 2) hf ht
  have hv : Continuous (Q.v t) := by
    have he : Q.v t = fun z => V t (z par.rev) • basisVec par := funext (P.v_shear t)
    rw [he]
    exact ((P.V_smooth t ht).continuous.comp (continuous_apply _)).smul continuous_const
  have hflux : (fun z => liftFluxX Q Cc (fun _ => f) 0 n t X z j) =
      fun z => ((Real.sqrt Q.η * Q.v t z j) • Φ X z -
        Real.sqrt Q.η • ∑ l : Fin 2, Q.G t X j l • fastPartial l Φ X z) -
        Q.η • ∑ l : Fin 2, Q.G t X j l • slowPartial l Ψ X z := by
    funext z
    simp only [liftFluxX, ite_eq_left hn, ite_true, Φ, Ψ, sub_eq_add_neg, neg_zero, add_zero]
  rw [hflux, covTruncCellMean_cross Q.η (Q.G t) (Q.v t) Φ Ψ hΦ hΨ hv X j]
  have hcoeff := setting_diagonal_mean_flux_coefficient_vector_apply P sX sZ Cc hseq
    n hn f j t ht X 0
  rw [hcoeff]
  by_cases hn2 : n = 2
  · have hm : (fun Y => fieldCellMean (Ψ Y)) = f := by
      funext Y
      have hi : Ψ Y = fun _ => f Y := by
        funext z
        dsimp [Ψ]
        rw [hn2]
        exact hseq.1 f hf t ht Y z
      rw [hi, fieldCellMean_const]
    rw [hm, hn2, ite_eq_left rfl]
    simp only [Φ, hn2, sub_eq_add_neg, neg_smul]
  · have hc : CoefField True 1 Ψ := liftApply_centField_of_seq Q hseq
      (by omega : 1 ≤ sX) (by omega : 1 ≤ sZ) (Nat.zero_le H)
      (Or.inl (by omega : 1 ≤ n - 2)) hf ht
    have hm : (fun Y => fieldCellMean (Ψ Y)) = fun _ => 0 :=
      funext (fun Y => hc.2 trivial Y)
    rw [hm, ite_eq_right hn2]
    simp only [fderiv_const_apply, zero_apply, smul_zero, Finset.sum_const_zero, Φ,
      sub_zero, add_zero]

end Setting
end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! **The commutator term of `G` at a terminal context**.

`covTruncComm_of_stmts : CovTruncCommStatement` from the statements `StreamArrayContStatement`,
`CommAdjContStatement`, `CommPriceStatement`, `CommDualStatement`. At a context with a large level
the gradient flux `∇ a_Z` is realized to the order `k_c + 6 p_T` (`covGrad_ctx_energy`), the
covariance size is `Ccov E^δ ρ²` (`covGrad_ledger`), the drift data are those of
`coarse_drift_small`, and `covComm_flux` gives the realization of `gCommTerm` of order
`k_c + 4 p_T` with mass `commPriceConst · √(|W|+1) √2 max(C_P,0) ‖f‖₂`, without a window factor.

Special cases:
- `f = 0`: the mass is `0`.
- `p_T = 0`: `commPriceConst = 0` and `gCommTerm = 0`. -/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route AVRegularity.EntryTerminal.CovGrad
open AVRegularity.CycleComparison.Coarse
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

namespace AVRegularity.EntryTerminal.CovComm

/-- The explicit drift derivative bound from the jets of the drift coefficient. -/
theorem commDrift_iter_le {v : Vec 2 → Vec 2} (hv : ContDiff ℝ (⊤ : ℕ∞) v) {a B₀ lam : ℝ}
    (ha : 0 ≤ a) (hB₀ : 0 ≤ B₀) (hlam : 0 < lam)
    (hj : ∀ l : ℕ, 1 ≤ l → ∀ x, ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
      a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) (l : ℕ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ (l + 1) v x‖ ≤ driftB a B₀ lam l := by
  have hv' : ContDiff ℝ ((l + 1 : ℕ) : ℕ∞) v := hv.of_le (by exact_mod_cast le_top)
  set X : ℝ := a * B₀ ^ (l + 1) * ((l + 1).factorial : ℝ) * lam ^ ((1 : ℤ) - ((l + 1 : ℕ) : ℤ))
  have hX : 0 ≤ X := by positivity
  have hk : ∀ k : Fin 2, ‖iteratedFDeriv ℝ (l + 1) (fun y => v y k) x‖ ≤ 2 ^ (l + 1) * X :=
    fun k => (norm_iteratedFDeriv_component_le hv' k x).trans
      (mul_le_mul_of_nonneg_left (hj (l + 1) (by omega) x) (by positivity))
  refine (norm_iteratedFDeriv_le_sum_components hv' x).trans ?_
  calc ∑ k : Fin 2, ‖iteratedFDeriv ℝ (l + 1) (fun y => v y k) x‖ ≤
        ∑ _k : Fin 2, 2 ^ (l + 1) * X := Finset.sum_le_sum fun k _ => hk k
    _ = 2 * (2 ^ (l + 1) * X) := by simp
    _ ≤ driftB a B₀ lam l := by
        have : 0 ≤ 2 ^ (l + 1) * X := by positivity
        unfold driftB
        change 2 * (2 ^ (l + 1) * X) ≤ 4 * 2 ^ (l + 1) * X
        nlinarith

/-- The uniform-in-order form of the time continuity of the derivative arrays. -/
theorem timeCont_of_arrays (hB : StreamArrayContStatement) {G : ℝ → Vec 2 → Vec 2}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => G q.1 q.2))
    (hp : ∀ s, AVenhance.IsZ2Periodic (G s)) (I : Set ℝ) (n : ℕ) : TimeCont G I n := by
  intro s₀ _ ε hε
  have key : ∀ n : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ s, |s - s₀| < δ → ∀ l ≤ n, ∀ x,
      ‖iteratedFDeriv ℝ (l + 1) (G s) x - iteratedFDeriv ℝ (l + 1) (G s₀) x‖ ≤ ε := by
    intro n
    induction n with
    | zero =>
      obtain ⟨δ, hδ, h⟩ := hB G hG hp 1 s₀ ε hε
      exact ⟨δ, hδ, fun s hs l hl x => by
        obtain rfl : l = 0 := by omega
        exact h s hs x⟩
    | succ n ih =>
      obtain ⟨δ₁, hδ₁, h₁⟩ := ih
      obtain ⟨δ₂, hδ₂, h₂⟩ := hB G hG hp (n + 2) s₀ ε hε
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs l hl x => ?_⟩
      rcases Nat.lt_or_ge l (n + 1) with hl' | hl'
      · exact h₁ s (lt_of_lt_of_le hs (min_le_left _ _)) l (by omega) x
      · obtain rfl : l = n + 1 := by omega
        exact h₂ s (lt_of_lt_of_le hs (min_le_right _ _)) x
  obtain ⟨δ, hδ, h⟩ := key n
  exact ⟨δ, hδ, fun s _ hs l hl x => h s hs l hl x⟩

theorem commPriceConst_mono (Kc p : ℕ) {ω ω' : ℝ} (hω : 0 ≤ ω) (h : ω ≤ ω') :
    commPriceConst Kc p ω ≤ commPriceConst Kc p ω' := by
  unfold commPriceConst
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) (by norm_num)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (by positivity)
  have h1 : ((Kc : ℝ) ^ 2 * ω) ≤ (Kc : ℝ) ^ 2 * ω' := mul_le_mul_of_nonneg_left h (by positivity)
  have h0 : 0 ≤ (Kc : ℝ) ^ 2 * ω := by positivity
  have h2 : (4 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc * ω) ≤ 4 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc * ω' :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have h3 : 0 ≤ (Kc : ℝ) ^ 2 * ω' := h0.trans h1
  have hc4 : 0 ≤ 4 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc := by positivity
  exact mul_le_mul (pow_le_pow_left₀ h0 h1 _) (mul_le_mul h2 (pow_le_pow_left₀ h0 h1 _)
    (pow_nonneg h0 _) (mul_nonneg hc4 (hω.trans h)))
    (mul_nonneg (mul_nonneg hc4 hω) (pow_nonneg h0 _)) (pow_nonneg h3 _)

theorem commCtx_contDiff_nat {f : Vec 2 → Vec 2} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    ContDiff ℝ (n : WithTop ℕ∞) f := hf.of_le (by exact_mod_cast le_top)

end AVRegularity.EntryTerminal.CovComm

namespace AVRegularity.Construction.Residual.Presentation

open AVRegularity.EntryTerminal.CovComm AVRegularity.EntryTerminal.CovGrad
  AVRegularity.CycleComparison.Coarse

/-- **The commutator term of `G`, from the five statements.** -/
theorem covTruncComm_of_stmts (hStream : StreamArrayContStatement) (hCont : CommAdjContStatement)
    (hPrice : CommPriceStatement) (hDual : CommDualStatement) : CovTruncCommStatement := by
  intro X
  obtain ⟨Λ₁, hΛ₁, hled⟩ := covGrad_ledger X
  obtain ⟨Λ₂, hΛ₂, hen⟩ := covGrad_ctx_energy X
  obtain ⟨ΛD, B₀, _, hΛD, hB₀, _, hdr⟩ := CycleComparison.Assembly.coarse_drift_small X.α X.s
    X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq X.ζ X.hζ
  refine ⟨max (max Λ₁ Λ₂) ΛD, le_trans hΛ₁ ((le_max_left _ _).trans (le_max_left _ _)),
    fun A hΛ hV => ?_⟩
  have hΛa : Λ₁ ≤ A.Λ := (le_max_left _ _).trans ((le_max_left _ _).trans hΛ)
  have hΛb : Λ₂ ≤ A.Λ := (le_max_right _ _).trans ((le_max_left _ _).trans hΛ)
  have hΛc : ΛD ≤ A.Λ := (le_max_right _ _).trans hΛ
  obtain ⟨Ccov, Cn, hCcov, hCn, hLed⟩ := hled A hΛa
  refine ⟨0, fun kc _ => ⟨0, 0, kc + 4 * A.pT + 2 * A.pT + 3,
    fun sXT sZT _ _ Kout hKout => ⟨0, ?_⟩⟩⟩
  intro Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hKO hcr0 hcr1 hcr hkS hc0 hKs hKan hLan hJm
    cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce cker hcP Cfl
  obtain ⟨Me, hMe⟩ := hen A hΛb hV cHP
  set Cstar : ℝ := commPriceConst (kc + 4 * A.pT + 2 * A.pT) A.pT Ccov *
    (Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) * (Real.sqrt 2 * max CP 0))
    with hCstar
  refine ⟨Cstar, 1, 1, one_pos, 1, 1, le_rfl, one_pos, ?_⟩
  intro C hC j₀ hj₀
  refine ⟨max Me 2, fun M hM c x => ?_⟩
  have hMe' : Me ≤ M := le_trans (le_max_left _ _) hM
  have hM2 : 2 ≤ M := le_trans (le_max_right _ _) hM
  have hkc : kc + 4 * A.pT + 2 * A.pT + 3 ≤ A.Khat Kout :=
    le_trans hKout (le_max_left _ _)
  have hF := hMe hMe' c x (kc + 4 * A.pT) hkc
  obtain ⟨hcov, hcovc, -, -⟩ := hLed hM2 c x
  obtain ⟨hDα, hDq, hDΛ, -, hstream, hband, -⟩ := c.data
  have hΛD' : 128 ≤ c.D.Λ := hDΛ ▸ le_trans hΛ₁ hΛa
  have hq1 : 1 < c.D.q := hDq ▸ X.hq.1
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) (le_trans hΛ₁ hΛa)
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos hΛ1 X.hζ hband (Nat.sub_le M 1)
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (le_trans (by norm_num) hΛD')
  have hcr1' : cr = 1 := x.one
  have hkey : ∀ y : ℝ, cr * y = y := fun y => by rw [hcr1', one_mul]
  have hρ : 0 < c.D.termRho cr M := by
    show 0 < cr * _
    rw [hkey]
    exact Real.sqrt_pos.2 (mul_pos hν hh)
  have hπ : ∀ v, 0 < c.Gw.mass c.lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛD' c.lawW v.1
  have hε := Scales.epsilon_basic (m := M - 1) hq1 hΛD'
  have hδ : 0 < ocDelta c.D.α c.D.q := by
    rw [hDα, hDq]
    exact (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).2.1
  have hω : 0 ≤ Ccov * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q :=
    mul_nonneg hCcov (Real.rpow_pos_of_pos hε.1 _).le
  have hωle : Ccov * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q ≤ Ccov :=
    mul_le_of_le_one_right hCcov (Real.rpow_le_one hε.1.le hε.2.1 hδ.le)
  obtain ⟨aD, lam, haD, hlam, hsm, hst, -, hjets, hsmooth, -, hper, -⟩ :=
    hdr A.Λ hΛc c.D.Φ hstream M c.D.κ hband M hM2 le_rfl (c.D.κ M) (c.D.κ (M - 1)) rfl rfl
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
  have hhyp : CommHyp (streamVel (c.D.Φ (M - 1)))
      (fun t => menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t) (Set.Icc c.tp (c.a + A.T₀))
      (kc + 4 * A.pT) A.pT
      ((Ccov * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q) * c.D.termRho cr M ^ 2)
      (driftB aD B₀ lam) :=
    { smooth := fun s _ => commCtx_contDiff_nat (hsmooth s) _
      periodic := fun s _ => hper s
      cov := fun s _ => hcov s
      drift := fun s _ l _ y => commDrift_iter_le (hsmooth s) haD hB₀0 hlam
        (fun l hl y => hjets l hl s y) l y }
  have hbc : TimeCont (streamVel (c.D.Φ (M - 1))) (Set.Icc c.tp (c.a + A.T₀))
      (kc + 4 * A.pT + 2 * A.pT) :=
    timeCont_of_arrays hStream
      (AVenhance.Infra.Construction.smoothPeriodic_streamVel (c.D.hΦ (M - 1))).smooth hper _ _
  have hreg : ∀ v : CompIn c.Gw.comps, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
      ContDiff ℝ ((kc + 4 * A.pT + 2 * A.pT + 1 : ℕ) : WithTop ℕ∞) (fun z => x.aZ t z v) ∧
        AVenhance.IsZ2Periodic (fun z => x.aZ t z v) := by
    intro v t ht
    have h1 := x.repZ v t ht
    exact ⟨h1.2.1.of_le (by exact_mod_cast
      (by omega : kc + 4 * A.pT + 2 * A.pT + 1 ≤ A.Khat Kout - 2)), h1.2.2.1⟩
  have hflux := covComm_flux hCont hPrice hDual (ι := CompIn c.Gw.comps)
    (h := fun v => ScalarH v.1.root) (kc + 4 * A.pT) A.pT
    (I := Set.Icc c.tp (c.a + A.T₀)) measurableSet_Icc (c.D.κ (M - 1)) (c.D.termRho cr M)
    (c.Gw.mass c.lawW) hν hρ hπ (streamVel (c.D.Φ (M - 1)))
    (fun t => menuCovPrimitive c.D (A.Mt M sXT sZT c.tp cr) M t)
    (Ccov * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q) aD B₀ lam (c.D.κ (M - 1))
    hcovc.continuousOn hbc hhyp hω haD hB₀ hlam hsmall hstrain hν.le
    (fun v t z => x.aZ t z v) _ hreg hF
  have hn : 0 ≤ c.normF := Real.sqrt_nonneg _
  have hP := commPriceConst_mono (kc + 4 * A.pT + 2 * A.pT) A.pT hω hωle
  have hS : 0 ≤ Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) * (Real.sqrt 2 * max CP 0) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (le_max_right _ _))
  have key : (c.D.κ (M - 1) * commPriceConst (kc + 4 * A.pT + 2 * A.pT) A.pT
        (Ccov * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q)) *
      (Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) *
        (Real.sqrt 2 * max CP 0 * c.normF) / c.D.κ (M - 1)) ≤ C * c.normF := by
    have e : (c.D.κ (M - 1) * commPriceConst (kc + 4 * A.pT + 2 * A.pT) A.pT
          (Ccov * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q)) *
        (Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) *
          (Real.sqrt 2 * max CP 0 * c.normF) / c.D.κ (M - 1)) =
        commPriceConst (kc + 4 * A.pT + 2 * A.pT) A.pT
          (Ccov * c.D.eps (M - 1) ^ ocDelta c.D.α c.D.q) *
        (Real.sqrt (((wordsUpTo A.alph (A.RT + 1)).card : ℝ) + 1) *
          (Real.sqrt 2 * max CP 0)) * c.normF := by
      field_simp
    rw [e]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP hS) hn).trans
      (mul_le_mul_of_nonneg_right hC hn)
  unfold CovTruncCommAt
  exact hasFluxBound_mono_Y hflux key

end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! **The commutator term of `G`.** `covTruncComm : CovTruncCommStatement`, from
the assembly `covTruncComm_of_stmts` and the proofs of its four statements: time continuity of
the derivative arrays (`streamArrayCont`), continuity of the vector adjoint (`commAdjCont`, using
`mulLip`), its price (`commPrice`) and the duality (`commDual`).

Special case: `p_T = 0` makes the term vanish and the bound trivial. -/

@[expose] public noncomputable section

namespace AVRegularity.Construction.Residual.Presentation

open AVRegularity.EntryTerminal.CovComm

/-- **The commutator term.** -/
theorem covTruncComm : CovTruncCommStatement :=
  covTruncComm_of_stmts streamArrayCont commAdjCont commPrice commDual

end AVRegularity.Construction.Residual.Presentation
end
end
end

section
section
/-! **The defect flux of a subset of the edges, and the sum of two such fluxes** (generic).

`FDData.filt P p` keeps the coefficients `P.B i j α` of the edges with `p i j α` and sets the
others to zero. `fdFilt_hasFluxBound` is `FDData.timeBound` for it, as a realized flux bound for
the flux with an `if` inside the sum over the edges. `hasFluxBound_add` adds two realized flux
bounds (through the proved difference `covTruncSub`).

Special cases: `p = fun _ _ _ => False` gives the flux `0`; `p = fun _ _ _ => True` is
`FDData.timeBound` itself. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
open AVRegularity.Construction.KernelDefect AVRegularity.KernelEnergy
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

open scoped Classical

variable {ι : Type*} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]

/-- The defect data with the coefficients of the edges outside `p` set to zero. -/
def FDData.filt (P : FDData ι h Γ) (p : ∀ i j, Γ i j → Prop) : FDData ι h Γ :=
  { P with
    B := fun i j α d => if p i j α then P.B i j α d else 0
    hB_meas := fun i j α d => by
      by_cases hp : p i j α
      · simpa only [hp, ite_true] using P.hB_meas i j α d
      · simp only [hp, ite_false]
        exact measurable_const
    hB_smooth := fun i j α d t ht => by
      by_cases hp : p i j α
      · simpa only [hp, ite_true] using P.hB_smooth i j α d t ht
      · simp only [hp, ite_false]
        exact contDiff_const
    hB_per := fun i j α d t ht => by
      by_cases hp : p i j α
      · simpa only [hp, ite_true] using P.hB_per i j α d t ht
      · simp only [hp, ite_false]
        intro k y
        rfl
    hB_fin := fun i j α d => by
      by_cases hp : p i j α
      · simpa only [hp, ite_true] using P.hB_fin i j α d
      · simp only [hp, ite_false]
        rw [CycleComparison.Coarse.coefficientSeminorm_zero_coefficient]
        exact ENNReal.zero_ne_top }

theorem FDData.filt_B_of (P : FDData ι h Γ) {p : ∀ i j, Γ i j → Prop} {i j : ι} {α : Γ i j}
    (hp : p i j α) (d : ↥(Finset.Icc 2 P.D)) : (P.filt p).B i j α d = P.B i j α d := by
  simp only [FDData.filt, hp, ite_true]

theorem FDData.filt_B_of_not (P : FDData ι h Γ) {p : ∀ i j, Γ i j → Prop} {i j : ι}
    {α : Γ i j} (hp : ¬ p i j α) (d : ↥(Finset.Icc 2 P.D)) : (P.filt p).B i j α d = 0 := by
  simp only [FDData.filt, hp, ite_false]

/-- **The defect flux of the edges in `p`, realized with the bound of `FDData.timeBound`.** -/
theorem fdFilt_hasFluxBound [∀ j, Nontrivial (h j)] (P : FDData ι h Γ)
    (p : ∀ i j, Γ i j → Prop) (ht01 : P.t₀ ≤ P.t₁) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (ν : ℝ)
    (hν : 0 < ν) (c : ℕ → ℝ) (hc : ∀ m, m + 2 ≤ P.D → 0 < c m) (θ : ℝ) (hθ : 0 ≤ θ)
    (hschur : SchurBound θ (kernelSchurMatrix (G := fun _ j _ => h j) ν P.ρ π P.k P.D P.t₀
      P.t₁ c (fun i j α => (P.Kern i j α).width)
      (fun _ j _ => ContinuousLinearMap.id ℝ (h j))
      (fun i j α d => if p i j α then P.B i j α d else 0)))
    {K : ℕ} (hK : P.OrderOK K) (V : ∀ j, ℝ → TorusHk (K + 1) (h j))
    (a : ∀ j, ℝ → Vec 2 → h j)
    (hcl : ∀ j, ∀ t ∈ Set.Icc P.t₀ P.t₁, IsClassicalRep (V j t) (a j t) (K + 1))
    (hmeas : ∀ j, AEStronglyMeasurable (V j) (volume.restrict (Set.Icc P.t₀ P.t₁)))
    (hint : Integrable (fun t => massGradNormSq (E := h) (K := fun _ => K) P.ρ π
      (fun j => (V j t).val)) (volume.restrict (Set.Icc P.t₀ P.t₁))) {E : ℝ}
    (hE : Real.sqrt (ν * ∫ s in Set.Icc P.t₀ P.t₁,
      massGradNormSq (E := h) (K := fun _ => K) P.ρ π (fun j => (V j s).val)) ≤ E) :
    HasFluxBound P.k (Set.Icc P.t₀ P.t₁) ν P.ρ π
      (fun i t x => ∑ j, ∑ α, if p i j α then ∑ d : ↥(Finset.Icc 2 P.D),
        P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          orderedDerivative word
            (fun y => a j t y - (P.Kern i j α).applyClassical P.φ₀ t (a j t) y) x) else 0)
      (P.q ^ P.L * P.Mconst c * θ * E) := by
  obtain ⟨Fk, hr, hm, hb⟩ := (P.filt p).timeBound ht01 π hπ ν hν c hc θ hθ hschur hK V a hcl
    hmeas hint
  refine ⟨Fk, ?_, hm, ?_⟩
  · intro i t ht
    filter_upwards [hr i t ht] with x hx
    refine hx.trans ?_
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ => ?_
    by_cases hp : p i j α
    · simp only [hp, ite_true]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [show (P.filt p).B i j α d = P.B i j α d from P.filt_B_of hp d]
      rfl
    · simp only [hp, ite_false]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [show (P.filt p).B i j α d = 0 from P.filt_B_of_not hp d]
      rfl
  · refine hb.trans ?_
    have h0 : 0 ≤ P.q ^ P.L * P.Mconst c * θ :=
      mul_nonneg (mul_nonneg (pow_nonneg P.hq0 _) (P.Mconst_nonneg hc)) hθ
    exact mul_le_mul_of_nonneg_left hE h0

/-- **The sum of two realized flux bounds.** -/
theorem hasFluxBound_add {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {k : ℕ} {I : Set ℝ} {ν ρ : ℝ} {π : ι → ℝ} (hν : 0 < ν) (hπ : ∀ v, 0 < π v)
    {F₁ F₂ : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} {Y₁ Y₂ : ℝ}
    (h₁ : HasFluxBound k I ν ρ π F₁ Y₁) (h₂ : HasFluxBound k I ν ρ π F₂ Y₂) :
    HasFluxBound k I ν ρ π (fun v t x => F₁ v t x + F₂ v t x) (Y₁ + Y₂) := by
  have h0 : HasFluxBound k I ν ρ π (fun v _ _ => (0 : PiLp 2 (fun _ : Fin 2 => h v))) 0 :=
    hasFluxBound_of_zero k I ν ρ π _ (fun v t _ => rfl) le_rfl
  have h2 := covTruncSub k I ν ρ π hν hπ _ _ _ _ h0 h₂
  have h3 := covTruncSub k I ν ρ π hν hπ _ _ _ _ h₁ h2
  have e : (fun v t x => F₁ v t x - (0 - F₂ v t x)) = fun v t x => F₁ v t x + F₂ v t x := by
    funext v t x
    abel
  rw [e, zero_add] at h3
  exact h3

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! **The root flux defect of a stage with two constant kernels is the sum of two filtered
defect fluxes** (generic).

For constant seed and fresh kernels `κw`, `κf` the kernel of an identity is `κw` if the kernel key
of its provenance is a seed key and `κf` otherwise (`kernelOf_const`). `rootFluxDefect_eq_add`
writes the root flux defect as `filtFlux … κw (sources, seed keys) + filtFlux … κf (sources,
fresh keys)`, with the classical representative extended by zero (`extAZ`).

Special cases: no seed keys gives `filtFlux … κw = 0`; `G' = G` and a single kernel. -/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

open scoped Classical

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The identity uses a seed kernel. -/
def IsSeedKernel (P : ProvParams) (G : GenStage D hr Dm b j₀) (v u : CompIn G.comps)
    (γ : G.fam.Γ v u) : Prop :=
  ∃ k, ((G.prov v u γ).tags P).kernel = .seed k

/-- With constant kernel families the kernel of an identity is `κw` or `κf`. -/
theorem kernelOf_const (P : ProvParams) (κw κf : KernelSpec) (G : GenStage D hr Dm b j₀)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
    G.kernelOf P (fun _ => κw) (fun _ => κf) v u γ = if IsSeedKernel P G v u γ then κw else κf := by
  unfold GenStage.kernelOf
  split
  · next k hk =>
    have h : IsSeedKernel P G v u γ := ⟨k, hk⟩
    simp only [h, ite_true]
  · next b' hk =>
    have h : ¬ IsSeedKernel P G v u γ := by
      rintro ⟨k, hk'⟩
      rw [hk] at hk'
      cases hk'
    simp only [h, ite_false]

/-- The classical representative `a_Z` of the sources, extended by zero to all components of
the extended stage. -/
def extAZ (G G' : GenStage D hr Dm b j₀) (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) :
    ∀ j : CompIn G'.comps, ℝ → Vec 2 → hr j.1.root :=
  fun j t y => if hj : j.1 ∈ G.comps then aZ t y ⟨j.1, hj⟩ else 0

/-- The defect flux of the edges in `p` with the kernel `κ` on the representative `a`. -/
def filtFlux (G' : GenStage D hr Dm b j₀) (φ₀ : Vec 2 → ℝ) (κ : KernelSpec)
    (p : ∀ v u : CompIn G'.comps, G'.fam.Γ v u → Prop)
    (a : ∀ j : CompIn G'.comps, ℝ → Vec 2 → hr j.1.root) (i : CompIn G'.comps) (t : ℝ)
    (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr i.1.root) :=
  ∑ j, ∑ α, if p i j α then ∑ d : ↥(Finset.Icc 2 Dm),
    G'.physCoeff i j α d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      orderedDerivative word (fun y => a j t y - κ.applyClassical φ₀ t (a j t) y) x) else 0

/-- **The root flux defect is the sum of the seed-kernel and the fresh-kernel defect fluxes.** -/
theorem rootFluxDefect_eq_add (P : ProvParams) (κw κf : KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G G' : GenStage D hr Dm b j₀) (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v' : CompIn G'.comps) (t : ℝ) (x : Vec 2) :
    rootFluxDefect P (fun _ => κw) (fun _ => κf) φ₀ G G' aZ v' t x =
      filtFlux G' φ₀ κw (fun v u γ => u.1 ∈ G.comps ∧ IsSeedKernel P G' v u γ) (extAZ G G' aZ)
        v' t x +
      filtFlux G' φ₀ κf (fun v u γ => u.1 ∈ G.comps ∧ ¬ IsSeedKernel P G' v u γ)
        (extAZ G G' aZ) v' t x := by
  unfold rootFluxDefect filtFlux
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : u.1 ∈ G.comps
  · simp only [hu, ↓reduceDIte]
    rw [← Finset.sum_add_distrib]
    have he : extAZ G G' aZ u t = fun y => aZ t y ⟨u.1, hu⟩ :=
      funext fun y => by simp only [extAZ, hu, ↓reduceDIte]
    refine Finset.sum_congr rfl fun γ _ => ?_
    by_cases hs : IsSeedKernel P G' v' u γ
    · simp only [hs, true_and, not_true_eq_false, ↓reduceIte, add_zero,
        kernelOf_const, he]
    · simp only [hs, true_and, not_false_eq_true, ↓reduceIte, zero_add,
        kernelOf_const, he]
  · simp only [hu, ↓reduceDIte, false_and, ↓reduceIte, Finset.sum_const_zero, add_zero]

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end

section
/-! **The realized bound of the root flux defect from the data of two filtered defect
fluxes** (generic over the stage).

`fdConst` is `FDData` with a constant kernel and the coefficients `physCoeff` of an extended stage
`G'`. `rootFlux_hasFluxBound` is the realized flux bound of `rootFluxDefect` with the constant
kernels `κw`, `κf`: the sum of `FDData.timeBound` for the sources in `G` with a seed kernel, and
for the sources in `G` with a fresh kernel. All remaining inputs are hypotheses: the regularity of
the coefficients, the two Schur bounds, the classical representative and its energy.

Special cases: no seed identity gives `θw = 0` admissible; `E = 0`. -/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
open AVRegularity.Construction.KernelDefect AVRegularity.KernelEnergy
open AVRegularity.Construction.Residual.Presentation AVRegularity

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

open scoped Classical

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The regularity of the coefficients of an extended stage on the window, at the order `k`. -/
def CoeffReg (G' : GenStage D hr Dm b j₀) (t₀ t₁ ρ : ℝ) (k : ℕ) : Prop :=
  ∀ (i j : CompIn G'.comps) (α : G'.fam.Γ i j) (d : ↥(Finset.Icc 2 Dm)),
    (Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => G'.physCoeff i j α d.1 p.1 p.2) ∧
    (∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (k : ℕ) (G'.physCoeff i j α d.1 t)) ∧
    (∀ t ∈ Set.Icc t₀ t₁, AVenhance.IsZ2Periodic (G'.physCoeff i j α d.1 t)) ∧
    coefficientSeminorm ρ k t₀ t₁ (G'.physCoeff i j α d.1) ≠ ⊤

/-- The coefficients of the edges in `p` (the others set to zero). -/
def filtCoeff (G' : GenStage D hr Dm b j₀) (p : ∀ v u : CompIn G'.comps, G'.fam.Γ v u → Prop)
    (i j : CompIn G'.comps) (α : G'.fam.Γ i j) (d : ↥(Finset.Icc 2 Dm)) :=
  if p i j α then G'.physCoeff i j α d.1 else 0

/-- The defect data with a constant kernel `κ` and the coefficients of the extended stage. -/
def fdConst (G' : GenStage D hr Dm b j₀) (φ₀ : Vec 2 → ℝ) (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnn : ∀ z, 0 ≤ φ₀ z) (hm : ∫ z, φ₀ z = 1)
    (hs : Function.support φ₀ ⊆ closedEuclideanUnitBall) (t₀ t₁ ρ : ℝ) (hρ : 0 < ρ) (k : ℕ)
    (hD : 2 ≤ Dm) (L : ℕ) (κ : KernelSpec) (hadm : κ.IsAdmissible 2 L) (hwpos : 0 < κ.width)
    (hwle : κ.width ≤ ρ) (hreg : CoeffReg G' t₀ t₁ ρ k) :
    FDData (CompIn G'.comps) (fun v => hr v.1.root) G'.fam.Γ where
  φ₀ := φ₀
  hφ := hφ
  hd := hd
  hnonneg := hnn
  hmass := hm
  hsupp := hs
  t₀ := t₀
  t₁ := t₁
  ρ := ρ
  hρ := hρ
  k := k
  D := Dm
  hD := hD
  L := L
  Γk := 2
  hΓk := by norm_num
  q := κ.width / ρ
  hq0 := div_nonneg hwpos.le hρ.le
  hq1 := (div_le_one hρ).2 hwle
  B := fun i j α d => G'.physCoeff i j α d.1
  hB_meas := fun i j α d => (hreg i j α d).1
  hB_smooth := fun i j α d => (hreg i j α d).2.1
  hB_per := fun i j α d => (hreg i j α d).2.2.1
  hB_fin := fun i j α d => (hreg i j α d).2.2.2
  Kern := fun _ _ _ => κ
  hadm := fun _ _ _ => hadm
  hwpos := fun _ _ _ => hwpos
  hwq := fun _ _ _ => le_of_eq (div_mul_cancel₀ _ hρ.ne').symm

/-- The price constant of the defect with the regularizer constants `1`. -/
def Mc (φ₀ : Vec 2 → ℝ) (L k D : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (D - 1),
    kdUniformMomentConst φ₀ L 2 * (((k + (L + m)).factorial : ℝ) / k.factorial)

theorem fdConst_Mconst (G' : GenStage D hr Dm b j₀) (φ₀ : Vec 2 → ℝ) (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnn : ∀ z, 0 ≤ φ₀ z) (hm : ∫ z, φ₀ z = 1)
    (hs : Function.support φ₀ ⊆ closedEuclideanUnitBall) (t₀ t₁ ρ : ℝ) (hρ : 0 < ρ) (k : ℕ)
    (hD : 2 ≤ Dm) (L : ℕ) (κ : KernelSpec) (hadm : κ.IsAdmissible 2 L) (hwpos : 0 < κ.width)
    (hwle : κ.width ≤ ρ) (hreg : CoeffReg G' t₀ t₁ ρ k) :
    (fdConst G' φ₀ hφ hd hnn hm hs t₀ t₁ ρ hρ k hD L κ hadm hwpos hwle hreg).Mconst (fun _ => 1) =
      Mc φ₀ L k Dm := by
  simp only [FDData.Mconst, fdConst, Mc, div_one]

theorem hasFluxBound_congr {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {k : ℕ} {I : Set ℝ} {ν ρ : ℝ} {π : ι → ℝ}
    {F F' : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} {Y : ℝ}
    (hF : ∀ v t x, F v t x = F' v t x) (hb : HasFluxBound k I ν ρ π F Y) :
    HasFluxBound k I ν ρ π F' Y := by
  obtain ⟨Fk, hrl, hm⟩ := hb
  exact ⟨Fk, fun v t ht => (hrl v t ht).trans (Filter.EventuallyEq.of_eq (funext (hF v t))), hm⟩

/-- **The realized bound of the root flux defect** from the two Schur bounds and the energy of
the classical representative. -/
theorem rootFlux_hasFluxBound [∀ r, Nontrivial (hr r)] (P : ProvParams) (φ₀ : Vec 2 → ℝ)
    (hφ : Integrable φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnn : ∀ z, 0 ≤ φ₀ z)
    (hm : ∫ z, φ₀ z = 1) (hs : Function.support φ₀ ⊆ closedEuclideanUnitBall)
    (κw κf : KernelSpec) (Lw Lf : ℕ) (haw : κw.IsAdmissible 2 Lw) (haf : κf.IsAdmissible 2 Lf)
    (hwposw : 0 < κw.width) (hwposf : 0 < κf.width)
    (G G' : GenStage D hr Dm b j₀) (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (t₀ t₁ ρ ν : ℝ) (hρ : 0 < ρ) (hwlew : κw.width ≤ ρ) (hwlef : κf.width ≤ ρ) (hν : 0 < ν)
    (ht01 : t₀ ≤ t₁) (k : ℕ) (hD : 2 ≤ Dm) (π : CompIn G'.comps → ℝ) (hπ : ∀ i, 0 < π i)
    (hreg : CoeffReg G' t₀ t₁ ρ k) (θw θf : ℝ) (hθw : 0 ≤ θw) (hθf : 0 ≤ θf)
    (hSw : SchurBound θw (kernelSchurMatrix (G := fun _ j _ => hr j.1.root) ν ρ π k Dm t₀ t₁
      (fun _ => 1) (fun _ _ _ => κw.width) (fun _ j _ => ContinuousLinearMap.id ℝ (hr j.1.root))
      (filtCoeff G' (fun v u γ => u.1 ∈ G.comps ∧ IsSeedKernel P G' v u γ))))
    (hSf : SchurBound θf (kernelSchurMatrix (G := fun _ j _ => hr j.1.root) ν ρ π k Dm t₀ t₁
      (fun _ => 1) (fun _ _ _ => κf.width) (fun _ j _ => ContinuousLinearMap.id ℝ (hr j.1.root))
      (filtCoeff G' (fun v u γ => u.1 ∈ G.comps ∧ ¬ IsSeedKernel P G' v u γ))))
    {K : ℕ} (hKw : k + (Dm - 2) + Lw ≤ K) (hKf : k + (Dm - 2) + Lf ≤ K)
    (V : ∀ j : CompIn G'.comps, ℝ → TorusHk (K + 1) (hr j.1.root))
    (hcl : ∀ j, ∀ t ∈ Set.Icc t₀ t₁, IsClassicalRep (V j t) (extAZ G G' aZ j t) (K + 1))
    (hmeas : ∀ j, AEStronglyMeasurable (V j) (volume.restrict (Set.Icc t₀ t₁)))
    (hint : Integrable (fun t => massGradNormSq (E := fun j : CompIn G'.comps => hr j.1.root)
      (K := fun _ => K) ρ π (fun j => (V j t).val)) (volume.restrict (Set.Icc t₀ t₁)))
    {E : ℝ} (hE : Real.sqrt (ν * ∫ s in Set.Icc t₀ t₁,
      massGradNormSq (E := fun j : CompIn G'.comps => hr j.1.root) (K := fun _ => K) ρ π
        (fun j => (V j s).val)) ≤ E) :
    HasFluxBound k (Set.Icc t₀ t₁) ν ρ π
      (fun v t x => rootFluxDefect P (fun _ => κw) (fun _ => κf) φ₀ G G' aZ v t x)
      ((κw.width / ρ) ^ Lw * Mc φ₀ Lw k Dm * θw * E +
        (κf.width / ρ) ^ Lf * Mc φ₀ Lf k Dm * θf * E) := by
  have h1 := fdFilt_hasFluxBound (fdConst G' φ₀ hφ hd hnn hm hs t₀ t₁ ρ hρ k hD Lw κw haw hwposw
    hwlew hreg) (fun v u γ => u.1 ∈ G.comps ∧ IsSeedKernel P G' v u γ) ht01 π hπ ν hν (fun _ => 1)
    (fun _ _ => one_pos) θw hθw hSw hKw V (extAZ G G' aZ) hcl hmeas hint hE
  have h2 := fdFilt_hasFluxBound (fdConst G' φ₀ hφ hd hnn hm hs t₀ t₁ ρ hρ k hD Lf κf haf hwposf
    hwlef hreg) (fun v u γ => u.1 ∈ G.comps ∧ ¬ IsSeedKernel P G' v u γ) ht01 π hπ ν hν
    (fun _ => 1) (fun _ _ => one_pos) θf hθf hSf hKf V (extAZ G G' aZ) hcl hmeas hint hE
  rw [fdConst_Mconst] at h1 h2
  exact hasFluxBound_congr (fun v t x => (rootFluxDefect_eq_add P κw κf φ₀ G G' aZ v t x).symm)
    (hasFluxBound_add hν hπ h1 h2)

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end
end
