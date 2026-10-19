-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Coarse.Defect.FcIdent
public import AVRegularity.Statements.Intermediate.CycleOutput.IsClassicalRep
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.EntryWeak.SobolevSummableMajorantBound
public import AVRegularity.EntryWeak.SourceParameterPeriodicity
import AVRegularity.Construction.Uniqueness.CellFieldUnique
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.CoupledEnergy.Variational.CarrierFiberCLM

/-! Time continuity of the retained coarse field and of its classical representative, for the
physical lift `û = 𝒯 a` (clause (f) of `cycle_comparison_physical_lift`).

1. The adjoint of the covariance polynomial `𝖯_p(H)` depends continuously (in operator norm) on
   the matrix `H`: its construction is a finite sum of compositions of the fixed adjoints of
   `∂_i ∂_j` with the scalars `H_{ij}`. Hence the retained field
   `W(t) = 𝖯_p(H_cov(t))^* ∑ U_{i,j}(t)` is continuous in time when the responses are, and the
   covariance `H_cov(t) = ∫_{t₀}^t (𝖩 - B I)` is continuous when `𝖩` is interval integrable.
2. A classical representative `a` of `V ∈ H^K(𝕋²; E)` at order `r` with `r + 2 ≤ K` satisfies
   `|∂^w a(x)| ≤ C ‖V‖` for every word of length at most `r` (the representative is, componentwise,
   the Fourier series of the field, `EntryWeakProofs.realClassicalLift`). Classical
   representatives are linear, so a continuous family of fields has classical representatives
   whose ordered derivatives are jointly continuous in time and space, uniformly in space. -/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev
open AVRegularity.CycleComparison.Coarse

namespace AVRegularity.CycleComparison.Reconstruction

/-! ### The adjoints of the transported operators -/

section AdjOps

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- Transport along an equality of operators does not change the adjoint maps. -/
theorem adj_ofOp {T T' : (Vec 2 → F) → (Vec 2 → E)} {m R Kc : ℕ} {C : ℝ} (h : T = T')
    (A : TorusAdj T m R Kc C) (K : ℕ) (hK : K + m ≤ Kc) :
    (A.ofOp h).adj K hK = A.adj K hK := by
  subst h
  rfl

/-- Transport along an equality of orders composes the adjoint with a Sobolev index cast. -/
theorem adj_ofOrder {T : (Vec 2 → F) → (Vec 2 → E)} {m m' R Kc : ℕ} {C : ℝ} (h : m = m')
    (A : TorusAdj T m R Kc C) (K : ℕ) (hK : K + m' ≤ Kc) :
    (A.ofOrder h).adj K hK =
      (A.adj K (by omega)).comp (torusCast (E := E) (by omega : K + m' = K + m)) := by
  subst h
  exact ContinuousLinearMap.ext fun _ => rfl

theorem adj_mono {T : (Vec 2 → F) → (Vec 2 → E)} {m R R' Kc Kc' : ℕ} {C C' : ℝ}
    (A : TorusAdj T m R Kc C) (hR : R' ≤ R) (hKc : Kc' ≤ Kc) (hC : C ≤ C') (K : ℕ)
    (hK : K + m ≤ Kc') : (A.mono hR hKc hC).adj K hK = A.adj K (hK.trans hKc) :=
  rfl

/-- The adjoint of a finite sum indexed by the members of a finset. -/
theorem adj_sumMem {ι : Type*} (s : Finset ι) {T : ι → (Vec 2 → F) → (Vec 2 → E)}
    {C : ι → ℝ} {m R Kc : ℕ} (A : ∀ i ∈ s, TorusAdj (T i) m R Kc (C i)) (K : ℕ)
    (hK : K + m ≤ Kc) :
    (TorusAdj.sumMem s A).adj K hK = ∑ i : s, (A i.1 i.2).adj K hK := by
  unfold TorusAdj.sumMem
  rw [adj_ofOp]
  rfl

/-- Scalar multiplication is the multiple of the identity. -/
theorem torusSmulCLM_eq_smul_id {K : ℕ} (c : ℝ) :
    (torusSmulCLM c : TorusHk K E →L[ℝ] TorusHk K E) =
      c • ContinuousLinearMap.id ℝ (TorusHk K E) :=
  ContinuousLinearMap.ext fun _ => rfl

theorem continuousOn_torusSmulCLM {K : ℕ} {c : ℝ → ℝ} {I : Set ℝ} (hc : ContinuousOn c I) :
    ContinuousOn (fun t => (torusSmulCLM (c t) : TorusHk K E →L[ℝ] TorusHk K E)) I :=
  (hc.smul (continuousOn_const (c := ContinuousLinearMap.id ℝ (TorusHk K E)))).congr
    fun t _ => torusSmulCLM_eq_smul_id (c t)

end AdjOps

/-! ### Continuity of the covariance adjoints in the matrix -/

section Cov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The adjoint of the covariance operator `∑_{ij} H_{ij} ∂_i ∂_j`. -/
theorem adj_covOp (H : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound H ≤ M) (R Kc K : ℕ)
    (hK : K + 2 ≤ Kc) :
    (TorusAdj.covOp (E := E) H hM R Kc).adj K hK =
      ∑ i : Fin 2, ∑ j : Fin 2,
        (torusSmulCLM (H i j)).comp ((TorusAdj.secondDeriv (E := E) i j R Kc).adj K hK) := by
  unfold TorusAdj.covOp
  rw [adj_ofOp]
  rfl

/-- The adjoint of `𝒞⁰`: the order cast `2 · 0 = 0` is a closed numeral identity, so the transport
reduces definitionally. -/
theorem adj_covIter_zero (H : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound H ≤ M)
    (R Kc K : ℕ) (hK : K + 2 * 0 ≤ Kc) :
    (TorusAdj.covIter (E := E) H hM 0 R Kc).adj K hK =
      (ContinuousLinearMap.id ℝ (TorusHk (K + 0) E)).comp
        (torusCast (E := E) (by omega : K + 2 * 0 = K + 0)) :=
  ContinuousLinearMap.ext fun _ => rfl

theorem adj_covIter_succ (H : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound H ≤ M)
    (l R Kc K : ℕ) (hK : K + 2 * (l + 1) ≤ Kc) :
    (TorusAdj.covIter (E := E) H hM (l + 1) R Kc).adj K hK =
      (((TorusAdj.covIter (E := E) H hM l (R + 2) Kc).adj K (by omega)).comp
        (((TorusAdj.covOp (E := E) H hM R Kc).adj (K + 2 * l) (by omega)).comp
          (torusCast (E := E) (by omega : K + (2 + 2 * l) = K + 2 * l + 2)))).comp
        (torusCast (E := E) (by omega : K + 2 * (l + 1) = K + (2 + 2 * l))) := by
  simp only [TorusAdj.covIter]
  rw [adj_ofOp, adj_ofOrder]
  rfl

theorem adj_covPolyP (H : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound H ≤ M)
    (p R Kc K : ℕ) (hK : K + 2 * p ≤ Kc) :
    (TorusAdj.covPolyP (E := E) H hM p R Kc).adj K hK =
      ∑ l : Finset.range (p + 1), (torusSmulCLM ((l.1.factorial : ℝ)⁻¹)).comp
        (((TorusAdj.covIter (E := E) H hM l.1 R Kc).adj K
            (by have := Finset.mem_range.mp l.2; omega)).comp
          (truncateTorusHk (E := E)
            (by have := Finset.mem_range.mp l.2; omega : K + 2 * l.1 ≤ K + 2 * p))) := by
  unfold TorusAdj.covPolyP
  rw [adj_ofOp, adj_mono, adj_sumMem]
  rfl

variable {I : Set ℝ} (Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (Mc : ℝ → ℝ)
  (hM : ∀ t, covBound (Hc t) ≤ Mc t)

theorem covOp_adj_continuousOn (hH : ∀ i j, ContinuousOn (fun t => Hc t i j) I) (R Kc K : ℕ)
    (hK : K + 2 ≤ Kc) :
    ContinuousOn (fun t => (TorusAdj.covOp (E := E) (Hc t) (hM t) R Kc).adj K hK) I := by
  have : ContinuousAdd (TorusHk (K + 2) E →L[ℝ] TorusHk K E) :=
    ContinuousLinearMap.isTopologicalAddGroup.toContinuousAdd
  refine ContinuousOn.congr ?_ fun t _ => adj_covOp (E := E) (Hc t) (hM t) R Kc K hK
  refine continuousOn_finsetSum _ fun i _ => ?_
  refine continuousOn_finsetSum _ fun j _ => ?_
  exact ContinuousOn.clm_comp (continuousOn_torusSmulCLM (E := E) (K := K) (hH i j))
    continuousOn_const

theorem covIter_adj_continuousOn (hH : ∀ i j, ContinuousOn (fun t => Hc t i j) I) :
    ∀ (l R Kc K : ℕ) (hK : K + 2 * l ≤ Kc),
      ContinuousOn (fun t => (TorusAdj.covIter (E := E) (Hc t) (hM t) l R Kc).adj K hK) I := by
  intro l
  induction l with
  | zero =>
    intro R Kc K hK
    refine ContinuousOn.congr ?_ fun t _ => adj_covIter_zero (E := E) (Hc t) (hM t) R Kc K hK
    exact continuousOn_const
  | succ l ih =>
    intro R Kc K hK
    refine ContinuousOn.congr ?_ fun t _ =>
      adj_covIter_succ (E := E) (Hc t) (hM t) l R Kc K hK
    exact ContinuousOn.clm_comp (ContinuousOn.clm_comp (ih (R + 2) Kc K (by omega))
      (ContinuousOn.clm_comp (covOp_adj_continuousOn Hc Mc hM hH R Kc (K + 2 * l) (by omega))
        continuousOn_const)) continuousOn_const

/-- **The adjoint of `𝖯_p(H)` is continuous in `H`.** -/
theorem covPolyP_adj_continuousOn (hH : ∀ i j, ContinuousOn (fun t => Hc t i j) I)
    (p R Kc K : ℕ) (hK : K + 2 * p ≤ Kc) :
    ContinuousOn (fun t => (TorusAdj.covPolyP (E := E) (Hc t) (hM t) p R Kc).adj K hK) I := by
  have : ContinuousAdd (TorusHk (K + 2 * p) E →L[ℝ] TorusHk K E) :=
    ContinuousLinearMap.isTopologicalAddGroup.toContinuousAdd
  refine ContinuousOn.congr ?_ fun t _ => adj_covPolyP (E := E) (Hc t) (hM t) p R Kc K hK
  refine continuousOn_finsetSum _ fun l _ => ?_
  exact ContinuousOn.clm_comp continuousOn_const (ContinuousOn.clm_comp
    (covIter_adj_continuousOn Hc Mc hM hH l.1 R Kc K
      (by have := Finset.mem_range.mp l.2; omega)) continuousOn_const)

end Cov

/-! ### The retained field -/

/-- **The retained field is continuous in time** when the responses and the covariance are. -/
theorem retainedW_continuousOn {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {k J H L p D : ℕ} {I : Set ℝ}
    (Hcov : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, ContinuousOn (fun t => Hcov t i j) I)
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (hU : ∀ i, i ≤ J → ∀ j, j ≤ H → ∀ v, ContinuousOn (U i j v) I)
    (hord : k + 1 + D + 2 * p ≤ k + 2 * L) (v : ι) :
    ContinuousOn (retainedW k J H L p D Hcov U hord v) I := by
  have h1 : ContinuousOn (fun t => respSum k J H L U (cellBox J H) v t) I := by
    show ContinuousOn (fun t => ∑ ij ∈ cellBox J H, respTrunc k J H L U ij v t) I
    refine continuousOn_finsetSum _ fun ij hij => ?_
    have hb := mem_cellBox hij
    by_cases hle : k + 2 * L ≤ coarseSlot k J H L ij.1 ij.2
    · refine ((truncateTorusHk (E := h v) hle).continuous.comp_continuousOn
        (hU ij.1 hb.1 ij.2 hb.2 v)).congr fun _ _ => ?_
      unfold respTrunc
      simp only [hle, ↓reduceDIte, Function.comp_apply]
    · refine (continuousOn_const (c := (0 : TorusHk (k + 2 * L) (h v)))).congr fun _ _ => ?_
      unfold respTrunc
      simp only [hle, ↓reduceDIte]
  have h2 : ContinuousOn (fun t => (TorusAdj.covPolyP (E := h v) (Hcov t) le_rfl p 0
      (k + 2 * L)).adj (k + 2 * L - 2 * p) (by omega)) I :=
    covPolyP_adj_continuousOn (E := h v) Hcov (fun t => covBound (Hcov t)) (fun _ => le_rfl)
      hH p 0 (k + 2 * L) (k + 2 * L - 2 * p) (by omega)
  have h3 := h2.clm_apply ((torusCast (E := h v)
    (by omega : k + 2 * L = k + 2 * L - 2 * p + 2 * p)).continuous.comp_continuousOn h1)
  exact (truncateTorusHk (E := h v)
    (by omega : k + 1 + D ≤ k + 2 * L - 2 * p)).continuous.comp_continuousOn h3

/-- The covariance `H_cov(t) = ∫_{t₀}^t (𝖩 - B I)` is continuous on the window when the entries of
`𝖩` are interval integrable. -/
theorem covarianceMatrix_entry_continuousOn {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {B t₀ t₁ : ℝ}
    (hJ : ∀ i j, IntervalIntegrable (fun s => Jm s i j) volume t₀ t₁) (i j : Fin 2) :
    ContinuousOn (fun t => covarianceMatrix Jm B t₀ t i j) (Set.Icc t₀ t₁) := by
  have hint : IntervalIntegrable
      (fun s => Jm s i j - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) volume t₀ t₁ :=
    (hJ i j).sub intervalIntegrable_const
  refine ((intervalIntegral.continuousOn_primitive_interval' hint Set.left_mem_uIcc).mono
    Set.Icc_subset_uIcc).congr fun _ _ => ?_
  simp only [covarianceMatrix, Matrix.of_apply]

/-- **The retained coarse field of a witness is continuous in time** on the window, given the
continuity of the covariance entries. -/
theorem coarseWitness_W_continuousOn_of_cov {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {t₀ t₁ B : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p k J L N : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ →
      TorusHk (coarseSlot k J H L i j) (PiLp 2 (fun _ : Fin 2 => h v))}
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hresp : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    (hwit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc)
    (hH : ∀ i j, ContinuousOn (fun t => covarianceMatrix Jm B t₀ t i j) (Set.Icc t₀ t₁))
    (hord : k + 1 + D + 2 * p ≤ k + 2 * L) (v : ι) :
    ContinuousOn (W v) (Set.Icc t₀ t₁) := by
  have hU : ∀ i, i ≤ J → ∀ j, j ≤ H → ∀ u, ContinuousOn (U i j u) (Set.Icc t₀ t₁) := by
    intro i hi j hj u
    obtain ⟨_, _, hsol, _⟩ := hresp i hi j hj
    exact hsol.1 u
  exact (retainedW_continuousOn (covarianceMatrix Jm B t₀) hH U hU hord v).congr fun _ ht =>
    witness_W_eq (covarianceMatrix Jm B t₀) U W hwit.1 hord ht v

/-- **The retained coarse field of a witness is continuous in time** on the window, when the
entries of `𝖩` are interval integrable on the window. -/
theorem coarseWitness_W_continuousOn {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {t₀ t₁ B : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p k J L N : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ →
      TorusHk (coarseSlot k J H L i j) (PiLp 2 (fun _ : Fin 2 => h v))}
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hresp : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    (hwit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc)
    (hJ : ∀ i j, IntervalIntegrable (fun s => Jm s i j) volume t₀ t₁)
    (hord : k + 1 + D + 2 * p ≤ k + 2 * L) (v : ι) :
    ContinuousOn (W v) (Set.Icc t₀ t₁) :=
  coarseWitness_W_continuousOn_of_cov hresp hwit (covarianceMatrix_entry_continuousOn hJ) hord v

/-! ### Quantitative embedding of classical representatives -/

section Embedding

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- The classical representative is `C^m` for `m ≤ r` (with the order cast used by the
ordered-derivative calculus). -/
theorem classicalRep_contDiff_le {K r m : ℕ} {V : TorusHk K E} {a : Vec 2 → E}
    (ha : IsClassicalRep V a r) (hm : m ≤ r) : ContDiff ℝ (m : ℕ∞) a := by
  have hr : ContDiff ℝ (r : ℕ∞) a := ha.2.1
  exact hr.of_le (by exact_mod_cast hm)

/-- A classical representative is a.e. the value class of the field. -/
theorem classicalRep_value_ae {K r : ℕ} {V : TorusHk K E} {a : Vec 2 → E}
    (ha : IsClassicalRep V a r) :
    a =ᵐ[volume.restrict AVenhance.unitCube] (V.val (valueIndex2 K) : Vec 2 → E) := by
  have h1 := ha.2.2.2 0 (Nat.zero_le r) Fin.elim0
  have h2 := AVRegularity.CycleComparison.Assembly.torusJetOrder_ae V (Nat.zero_le K) Fin.elim0
  have hα : (⟨⟨0, Nat.lt_succ_of_le (Nat.zero_le K)⟩, Fin.elim0⟩ : JetIndex2 K) =
      valueIndex2 K := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext z
      exact Fin.elim0 z
  rw [hα] at h2
  rw [AVRegularity.orderedDerivative_zero] at h1
  exact h1.symm.trans h2

/-- The inner products of a classical representative with a fixed vector are the Fourier
representatives of the corresponding scalar fields. -/
theorem classicalRep_inner_eq {K r : ℕ} (hr : r + 2 ≤ K) {V : TorusHk K E} {a : Vec 2 → E}
    (ha : IsClassicalRep V a r) (e : E) :
    (fun x => inner ℝ e (a x)) = AVRegularity.EntryWeakProofs.realClassicalLift K
      (AVRegularity.CoupledEnergy.Variational.mapTorusHk (innerSL ℝ e) V) := by
  apply AVRegularity.Uniqueness.eq_of_ae_eq_periodic
  · exact continuous_const.inner ha.2.1.continuous
  · exact (AVRegularity.EntryWeakProofs.realClassicalLift_contDiff K 0 (by omega) _).continuous
  · intro n x
    show inner ℝ e (a (x + AVenhance.latticeShift n)) = inner ℝ e (a x)
    rw [ha.2.2.1 n x]
  · exact AVRegularity.EntryWeakProofs.realClassicalLift_periodic K _
  · have h1 := classicalRep_value_ae ha
    have h2 := AVRegularity.CoupledEnergy.Variational.mapTorusHk_jet_ae (innerSL ℝ e) V
      (valueIndex2 K)
    have h3 := AVRegularity.EntryWeakProofs.realClassicalLift_value_ae K (by omega)
      (AVRegularity.CoupledEnergy.Variational.mapTorusHk (innerSL ℝ e) V)
    filter_upwards [h1, h2, h3] with x e1 e2 e3
    rw [e3, e2, innerSL_apply_apply, e1]

/-- **Sup bound of the classical derivatives** (`H^{r+2}(𝕋²) ⊂ C^r`, quantitatively). -/
theorem classicalRep_orderedDerivative_le [FiniteDimensional ℝ E] (K r : ℕ) (hr : r + 2 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : TorusHk K E) (a : Vec 2 → E), IsClassicalRep V a r →
      ∀ m, m ≤ r → ∀ (w : DerivativeWord2 m) (x : Vec 2),
        ‖orderedDerivative w a x‖ ≤ C * ‖V‖ := by
  have hc : ∀ n : ℕ, 0 ≤ AVRegularity.EntryWeakProofs.classicalSobolevConstant n := fun n => by
    unfold AVRegularity.EntryWeakProofs.classicalSobolevConstant
    positivity
  refine ⟨(∑ n ∈ Finset.range (r + 1), AVRegularity.EntryWeakProofs.classicalSobolevConstant n) *
      ∑ i, ‖AVRegularity.CoupledEnergy.Variational.mapTorusHkCLM K
        (innerSL ℝ (stdOrthonormalBasis ℝ E i))‖,
    mul_nonneg (Finset.sum_nonneg fun n _ => hc n) (Finset.sum_nonneg fun i _ =>
      ContinuousLinearMap.opNorm_nonneg (AVRegularity.CoupledEnergy.Variational.mapTorusHkCLM K
        (innerSL ℝ (stdOrthonormalBasis ℝ E i)))),
    fun V a ha m hm w x => ?_⟩
  have hcm : AVRegularity.EntryWeakProofs.classicalSobolevConstant m ≤
      ∑ n ∈ Finset.range (r + 1), AVRegularity.EntryWeakProofs.classicalSobolevConstant n :=
    Finset.single_le_sum (fun n _ => hc n) (Finset.mem_range.2 (by omega))
  have ham : ContDiff ℝ (m : ℕ∞) a := classicalRep_contDiff_le ha hm
  have hcomp : ∀ i, |inner ℝ (stdOrthonormalBasis ℝ E i) (orderedDerivative w a x)| ≤
      AVRegularity.EntryWeakProofs.classicalSobolevConstant m *
        ‖AVRegularity.CoupledEnergy.Variational.mapTorusHkCLM K
          (innerSL ℝ (stdOrthonormalBasis ℝ E i))‖ * ‖V‖ := by
    intro i
    have h1 := AVRegularity.orderedDerivative_clm_comp
      (innerSL ℝ (stdOrthonormalBasis ℝ E i)) w ham
    have h2 := classicalRep_inner_eq hr ha (stdOrthonormalBasis ℝ E i)
    have h3 : inner ℝ (stdOrthonormalBasis ℝ E i) (orderedDerivative w a x) =
        orderedDerivative w (AVRegularity.EntryWeakProofs.realClassicalLift K
          (AVRegularity.CoupledEnergy.Variational.mapTorusHk
            (innerSL ℝ (stdOrthonormalBasis ℝ E i)) V)) x := by
      rw [← h2]
      have h4 := congrFun h1 x
      simp only [innerSL_apply_apply] at h4
      exact h4.symm
    have hV : ‖AVRegularity.CoupledEnergy.Variational.mapTorusHk
          (innerSL ℝ (stdOrthonormalBasis ℝ E i)) V‖ ≤
        ‖AVRegularity.CoupledEnergy.Variational.mapTorusHkCLM K
          (innerSL ℝ (stdOrthonormalBasis ℝ E i))‖ * ‖V‖ := by
      rw [← AVRegularity.CoupledEnergy.Variational.mapTorusHkCLM_apply]
      exact ContinuousLinearMap.le_opNorm _ _
    calc |inner ℝ (stdOrthonormalBasis ℝ E i) (orderedDerivative w a x)|
        = ‖orderedDerivative w (AVRegularity.EntryWeakProofs.realClassicalLift K
            (AVRegularity.CoupledEnergy.Variational.mapTorusHk
              (innerSL ℝ (stdOrthonormalBasis ℝ E i)) V)) x‖ := by
          rw [h3, Real.norm_eq_abs]
      _ ≤ ‖iteratedFDeriv ℝ m (AVRegularity.EntryWeakProofs.realClassicalLift K
            (AVRegularity.CoupledEnergy.Variational.mapTorusHk
              (innerSL ℝ (stdOrthonormalBasis ℝ E i)) V)) x‖ :=
          AVRegularity.norm_orderedDerivative_le
            (AVRegularity.EntryWeakProofs.realClassicalLift_contDiff K m (by omega) _) w x
      _ ≤ AVRegularity.EntryWeakProofs.classicalSobolevConstant m *
            ‖AVRegularity.CoupledEnergy.Variational.mapTorusHk
              (innerSL ℝ (stdOrthonormalBasis ℝ E i)) V‖ :=
          AVRegularity.EntryWeakProofs.realClassicalLift_derivative_norm_le K _ m (by omega) x
      _ ≤ AVRegularity.EntryWeakProofs.classicalSobolevConstant m *
            (‖AVRegularity.CoupledEnergy.Variational.mapTorusHkCLM K
              (innerSL ℝ (stdOrthonormalBasis ℝ E i))‖ * ‖V‖) :=
          mul_le_mul_of_nonneg_left hV (hc m)
      _ = _ := (mul_assoc _ _ _).symm
  have hrepr := (stdOrthonormalBasis ℝ E).sum_repr' (orderedDerivative w a x)
  calc ‖orderedDerivative w a x‖
      = ‖∑ i, inner ℝ (stdOrthonormalBasis ℝ E i) (orderedDerivative w a x) •
          stdOrthonormalBasis ℝ E i‖ := by rw [hrepr]
    _ ≤ ∑ i, ‖inner ℝ (stdOrthonormalBasis ℝ E i) (orderedDerivative w a x) •
          stdOrthonormalBasis ℝ E i‖ := norm_sum_le _ _
    _ = ∑ i, |inner ℝ (stdOrthonormalBasis ℝ E i) (orderedDerivative w a x)| :=
        Finset.sum_congr rfl fun i _ => by
          rw [norm_smul, (stdOrthonormalBasis ℝ E).orthonormal.1 i, mul_one, Real.norm_eq_abs]
    _ ≤ ∑ i, AVRegularity.EntryWeakProofs.classicalSobolevConstant m *
          ‖AVRegularity.CoupledEnergy.Variational.mapTorusHkCLM K
            (innerSL ℝ (stdOrthonormalBasis ℝ E i))‖ * ‖V‖ :=
        Finset.sum_le_sum fun i _ => hcomp i
    _ = AVRegularity.EntryWeakProofs.classicalSobolevConstant m *
          (∑ i, ‖AVRegularity.CoupledEnergy.Variational.mapTorusHkCLM K
            (innerSL ℝ (stdOrthonormalBasis ℝ E i))‖) * ‖V‖ := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (∑ n ∈ Finset.range (r + 1), AVRegularity.EntryWeakProofs.classicalSobolevConstant n) *
          (∑ i, ‖AVRegularity.CoupledEnergy.Variational.mapTorusHkCLM K
            (innerSL ℝ (stdOrthonormalBasis ℝ E i))‖) * ‖V‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcm
          (Finset.sum_nonneg fun _ _ => ContinuousLinearMap.opNorm_nonneg _)) (norm_nonneg _)

/-- Classical representatives are linear: the representative of `V - V'` is `a - a'`. -/
theorem isClassicalRep_sub {K r : ℕ} {V V' : TorusHk K E} {a a' : Vec 2 → E}
    (ha : IsClassicalRep V a r) (ha' : IsClassicalRep V' a' r) :
    IsClassicalRep (V - V') (fun x => a x - a' x) r := by
  refine ⟨ha.1, ha.2.1.sub ha'.2.1, fun n x => ?_, fun m hm w => ?_⟩
  · show a (x + AVenhance.latticeShift n) - a' (x + AVenhance.latticeShift n) = a x - a' x
    rw [ha.2.2.1 n x, ha'.2.2.1 n x]
  · have hmK : m ≤ K := hm.trans ha.1
    have hD : orderedDerivative w (fun x => a x - a' x) =
        fun x => orderedDerivative w a x - orderedDerivative w a' x :=
      AVRegularity.orderedDerivative_sub w (classicalRep_contDiff_le ha hm)
        (classicalRep_contDiff_le ha' hm)
    have h1 := AVRegularity.CycleComparison.Assembly.torusJetOrder_ae (V - V') hmK w
    have h2 := AVRegularity.CycleComparison.Assembly.torusJetOrder_ae V hmK w
    have h3 := AVRegularity.CycleComparison.Assembly.torusJetOrder_ae V' hmK w
    have h4 := Lp.coeFn_sub (V.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩)
      (V'.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩)
    filter_upwards [h1, h2, h3, h4, ha.2.2.2 m hm w, ha'.2.2.2 m hm w]
      with x e1 e2 e3 e4 e5 e6
    calc torusJetOrder (V - V') m w x
        = ((V.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩ : Vec 2 → E) -
            (V'.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩ : Vec 2 → E)) x := e1.trans e4
      _ = (V.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩ : Vec 2 → E) x -
            (V'.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩ : Vec 2 → E) x := rfl
      _ = torusJetOrder V m w x - torusJetOrder V' m w x := by rw [e2, e3]
      _ = orderedDerivative w a x - orderedDerivative w a' x := by rw [e5, e6]
      _ = orderedDerivative w (fun x => a x - a' x) x := by rw [hD]

/-- **Lipschitz dependence of the classical derivatives on the field**, uniformly in space. -/
theorem classicalRep_orderedDerivative_sub_le [FiniteDimensional ℝ E] (K r : ℕ)
    (hr : r + 2 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V V' : TorusHk K E) (a a' : Vec 2 → E), IsClassicalRep V a r →
      IsClassicalRep V' a' r → ∀ m, m ≤ r → ∀ (w : DerivativeWord2 m) (x : Vec 2),
        ‖orderedDerivative w a x - orderedDerivative w a' x‖ ≤ C * ‖V - V'‖ := by
  obtain ⟨C, hC, hb⟩ := classicalRep_orderedDerivative_le (E := E) K r hr
  refine ⟨C, hC, fun V V' a a' ha ha' m hm w x => ?_⟩
  have hD : orderedDerivative w (fun x => a x - a' x) =
      fun x => orderedDerivative w a x - orderedDerivative w a' x :=
    AVRegularity.orderedDerivative_sub w (classicalRep_contDiff_le ha hm)
      (classicalRep_contDiff_le ha' hm)
  calc ‖orderedDerivative w a x - orderedDerivative w a' x‖
      = ‖orderedDerivative w (fun x => a x - a' x) x‖ := by rw [hD]
    _ ≤ C * ‖V - V'‖ := hb _ _ (isClassicalRep_sub ha ha') m hm w x

end Embedding

end AVRegularity.CycleComparison.Reconstruction
