-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Coarse.Energy.Cell
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! Pieces of one step of the letter recursion: the initial datum of a cell carries at most the
mass norm of the input (and nothing off the corner cell); the energy right side of a cell splits
into its initial and flux parts; the value fields of the truncated predecessors are those of the
predecessors; the gradient norm of a truncated predecessor is at most the gradient factorial norm
of its gradient-level field. -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] [CompleteSpace E] in
theorem factorialNormSq_zero_jet (ρ : ℝ) {μ : Measure (Vec 2)} {K : ℕ} :
    factorialNormSq ρ (0 : JetL2 μ K E) = 0 :=
  le_antisymm (Real.sqrt_eq_zero'.1 (sqrt_fNSq_zero ρ)) (factorialNormSq_nonneg ρ _)

theorem gradNormSq_zero (ρ : ℝ) {K : ℕ} : gradNormSq (K := K) ρ (0 : TorusHk (K + 1) E) = 0 := by
  unfold gradNormSq
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_zero]
  exact factorialNormSq_zero_jet ρ

theorem truncateTorusHk_truncateTorusHk {K M M' : ℕ} (h1 : K ≤ M) (h2 : M ≤ M')
    (X : TorusHk M' E) :
    truncateTorusHk h1 (truncateTorusHk h2 X) = truncateTorusHk (h1.trans h2) X :=
  rfl

end General

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

omit [DecidableEq ι] in
/-- **The initial datum of a cell.** -/
theorem initial_mass_le {N K : ℕ} (hKN : K ≤ N) (f : ∀ v, TorusHk N (h v))
    (f₀ : ∀ v, TorusHk K (h v)) (i j : ℕ)
    (hf₀ : if i = 0 ∧ j = 0 then
        ∀ v, (f₀ v).toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
          (f v).toFunction.jet (valueIndex2 N)
       else ∀ v, f₀ v = 0)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (ρ : ℝ) :
    ∑ v, (π v)⁻¹ * factorialNormSq ρ (f₀ v).val ≤
      if i = 0 ∧ j = 0 then massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val)
      else 0 := by
  split_ifs at hf₀ ⊢ with h00
  · unfold massNormSq
    refine Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (hπ v).le)
    have he : f₀ v = truncateTorusHk hKN (f v) := torusHk_eq_of_cellInner fun ψ _ _ => by
      rw [tval_truncateTorusHk]
      unfold cellInner
      exact integral_congr_ae ((hf₀ v).mono fun x hx => by simp only [tval]; rw [hx])
    have h1 : Real.sqrt (factorialNormSq ρ (truncateTorusHk hKN (f v)).val) ≤
        Real.sqrt (factorialNormSq ρ (f v).val) := sqrt_fNSq_truncate_le ρ hKN (f v).val
    rw [he]
    exact (Real.sqrt_le_sqrt_iff (factorialNormSq_nonneg ρ _)).1 h1
  · refine le_of_eq (Finset.sum_eq_zero fun v _ => ?_)
    rw [hf₀ v]
    have : factorialNormSq ρ (0 : TorusHk K (h v)).val = 0 := factorialNormSq_zero_jet ρ
    rw [this, mul_zero]

omit [DecidableEq ι] in
/-- **The energy right side of a cell splits into its initial and flux parts.** -/
theorem compRHS_sum_eq {ρ B t₀ t₁ : ℝ} {π : ι → ℝ} {K : ℕ} (f₀ : ∀ v, TorusHk K (h v))
    (G : ∀ v, ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => h v)))
    (hG : ∀ v, MemLp (G v) 2 (volume.restrict (Set.Icc t₀ t₁))) :
    ∑ v, compRHS ρ B t₀ t₁ (π v) (f₀ v) (G v) =
      6 * ∑ v, (π v)⁻¹ * factorialNormSq ρ (f₀ v).val +
        24 / B * ∫ s in Set.Icc t₀ t₁, ∑ v, (π v)⁻¹ * factorialNormSq ρ (G v s).val := by
  rw [integral_finsetSum _ fun v _ => (integrable_factorialNormSq_torus (hG v)).const_mul _]
  unfold compRHS
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by ring

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The value fields of truncated predecessors. -/
theorem predV_eq_of_tval {K K' : ℕ} (n : ℕ) (V : ∀ v, ℝ → TorusHk K' (h v))
    (W : ∀ v, ℝ → TorusHk K (h v)) (hW : n ≠ 0 → ∀ v s, tval (W v s) = tval (V v s)) :
    predV n W = (if n = 0 then fun _ _ _ => 0
      else fun v s x => (V v s).toFunction.jet (valueIndex2 K') x) := by
  by_cases hn : n = 0
  · simp only [predV, hn, ↓reduceIte]
  · simp only [predV, hn, ↓reduceIte]
    funext v s x
    rw [hW hn v s]
    rfl

/-- The truncated predecessor family: the predecessor truncated to the order of the adjoints,
zero when absent. -/
def truncPred {K K' : ℕ} (n : ℕ) (hle : n ≠ 0 → K ≤ K') (V : ∀ v, ℝ → TorusHk K' (h v)) :
    ∀ v, ℝ → TorusHk K (h v) :=
  fun v s => if hn : n = 0 then 0 else truncateTorusHk (hle hn) (V v s)

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem tval_truncPred {K K' : ℕ} {n : ℕ} (hle : n ≠ 0 → K ≤ K')
    (V : ∀ v, ℝ → TorusHk K' (h v)) (hn : n ≠ 0) (v : ι) (s : ℝ) :
    tval (truncPred n hle V v s) = tval (V v s) := by
  simp only [truncPred, hn, ↓reduceDIte]
  exact tval_truncateTorusHk _ _

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- **The gradient norm of a truncated predecessor.** -/
theorem gradNormSq_truncPred_le {K M : ℕ} {n : ℕ} (hle : n ≠ 0 → K + 1 ≤ M) (ρ : ℝ)
    (V : ∀ v, ℝ → TorusHk M (h v)) (Vw : ∀ v, ℝ → TorusHk (M + 1) (h v)) {s : ℝ} (v : ι)
    (hV : n ≠ 0 → truncateTorusHk (Nat.le_succ M) (Vw v s) = V v s) :
    gradNormSq (K := K) ρ (truncPred n hle V v s) ≤ gradFactorialNormSq ρ (Vw v s).val := by
  by_cases hn : n = 0
  · simp only [truncPred, hn, ↓reduceDIte]
    rw [gradNormSq_zero]
    exact gradFactorialNormSq_nonneg ρ _
  · have hKM : K ≤ M := by have := hle hn; omega
    simp only [truncPred, hn, ↓reduceDIte]
    rw [← hV hn, truncateTorusHk_truncateTorusHk]
    exact gradNormSq_le_of_truncate hKM ρ _ (Vw v s) rfl

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! The fluxes of any coarse response family are square integrable in time: on the window each
flux agrees with the flux constructed from the same predecessors (uniqueness of the
response-flux identity), which is square integrable. -/

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

/-- Two fluxes with the same response-flux identity agree on the window. -/
theorem responseFlux_unique {K : ℕ}
    {G G' : ∀ v, ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => h v))} {U' U'' : ∀ v, ℝ → Vec 2 → h v}
    (hG : IsCoarseResponseFlux t₀ t₁ b D H p AD CE (covarianceMatrix Jm B t₀) K G U' U'')
    (hG' : IsCoarseResponseFlux t₀ t₁ b D H p AD CE (covarianceMatrix Jm B t₀) K G' U' U'')
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v : ι) : G v s = G' v s := by
  refine torusHk_eq_of_cellInner fun ψ hψ hp => ?_
  have h1 := responseFlux_component hG hs v ψ hψ hp
  have h2 := responseFlux_component hG' hs v ψ hψ hp
  exact h1.trans h2.symm

/-- **The fluxes of a coarse response family are square integrable.** -/
theorem coarseResponses_flux_memLp
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {i j : ℕ} (hi : i ≤ J) (hj : j ≤ H) (v : ι) :
    MemLp (G i j v) 2 (volume.restrict (Set.Icc t₀ t₁)) := by
  obtain ⟨_, _, _, hflux⟩ := hR i hi j hj
  have hU' : i ≠ 0 → ∀ w, ContinuousOn (U (i - 1) j w) (Set.Icc t₀ t₁) := fun hi0 w => by
    obtain ⟨_, _, hsol, _⟩ := hR (i - 1) (by omega) j hj
    exact hsol.1 w
  have hU'' : j ≠ 0 → ∀ w, ContinuousOn (U i (j - 1) w) (Set.Icc t₀ t₁) := fun hj0 w => by
    obtain ⟨_, _, hsol, _⟩ := hR i hi (j - 1) (by omega)
    exact hsol.1 w
  obtain ⟨G', hG'm, hG'⟩ := hasCellFlux_of_setting P hi hj (U (i - 1) j) (U i (j - 1)) hU' hU''
  have heq : ∀ s ∈ Set.Icc t₀ t₁, G i j v s = G' v s := fun s hs =>
    responseFlux_unique hflux hG' hs v
  exact (hG'm v).ae_eq ((ae_restrict_iff' measurableSet_Icc).2
    (Filter.Eventually.of_forall fun s hs => (heq s hs).symm))

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! **One step of the letter recursion.** The strong energy of the cell `(i,j)` of a coarse
response family is at most `√6 |f|` on the corner cell, plus the diagonal step factor times the
energy of the diagonal predecessor, plus the edge step factor times the energy of the edge
predecessor: the energy bound of the cell, the gradient-form adjoint bounds of the response flux
at every time, the mass-weighted Schur test and the gradient part of the predecessor energies. -/

section
/-- The order of the gradient adjoints of the cell `(i,j)`. -/
abbrev cellKc (k J H L p D i j : ℕ) : ℕ := coarseSlot k J H L i j + (4 * p + D - 1 + 1)

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

/-- **One step of the letter recursion.** -/
theorem cell_step
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    (hC : 0 ≤ Cstar) (hΘ : 0 ≤ Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {i j : ℕ} (hi : i ≤ J) (hj : j ≤ H) :
    strongEnergy ρ B π t₀ t₁ (U i j) (Uw i j) ≤
      ENNReal.ofReal (Real.sqrt 6 * Real.sqrt (if i = 0 ∧ j = 0 then
        massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val) else 0)) +
      (if i = 0 then 0 else
        ENNReal.ofReal (Real.sqrt 48 * cellCgD ρ a B₀
          (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal (cellKc k J H L p D i j) D p
            t₀ t₁ AD / B) * strongEnergy ρ B π t₀ t₁ (U (i - 1) j) (Uw (i - 1) j)) +
      (if j = 0 then 0 else
        ENNReal.ofReal (Real.sqrt 48 * edgeS (cellKc k J H L p D i j) D H p B Cstar Θ / B) *
          strongEnergy ρ B π t₀ t₁ (U i (j - 1)) (Uw i (j - 1))) := by
  obtain ⟨f₀, hf₀, hsol, hflux⟩ := hR i hi j hj
  obtain ⟨_, _, hsolD, _⟩ := hR (i - 1) (by omega) j hj
  obtain ⟨_, _, hsolE, _⟩ := hR i hi (j - 1) (by omega)
  have hρ := P.rho_pos
  have hB := P.B_pos
  have hσ : 0 ≤ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal := ENNReal.toReal_nonneg
  have hKN : coarseSlot k J H L i j + L ≤ N := coarseSlot_add_le k J H L N i j P.N_eq
  have hL := P.L_eq
  have hD := P.D_ge
  have hKc1 : cellKc k J H L p D i j + 1 ≤ N := by unfold cellKc; omega
  have hKcN : cellKc k J H L p D i j ≤ N := by omega
  have hle1 : i ≠ 0 → coarseSlot k J H L i j + (4 * p + D - 1 + 1) ≤
      coarseSlot k J H L (i - 1) j := fun hi0 => by
    rw [coarseSlot_diagonal_predecessor k J H L i j (by omega) hi hj]; omega
  have hle2 : j ≠ 0 → coarseSlot k J H L i j + (4 * p + D - 1 + 1) ≤
      coarseSlot k J H L i (j - 1) := fun hj0 => by
    rw [coarseSlot_edge_predecessor k J H L i j (by omega) hi hj]; omega
  have hGm := fun v => coarseResponses_flux_memLp P hR hi hj v
  -- the energy of the cell
  have hE0 := response_strongEnergy_le P (by omega) hGm hsol
  rw [compRHS_sum_eq f₀ (G i j) hGm] at hE0
  -- the pointwise flux bound
  have hpt : ∀ s ∈ Set.Icc t₀ t₁, ∀ v,
      Real.sqrt (factorialNormSq ρ (G i j v s).val) ≤
        (if i = 0 then 0 else cellCgD ρ a B₀
          (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal (cellKc k J H L p D i j) D p
            t₀ t₁ AD * Real.sqrt (gradNormSq (K := coarseSlot k J H L i j + (4 * p + D - 1)) ρ
              (truncPred i hle1 (U (i - 1) j) v s))) +
        ∑ u, (if j = 0 then 0 else cellCgE ρ (cellKc k J H L p D i j) D H p t₀ t₁ CE v u *
          Real.sqrt (gradNormSq (K := coarseSlot k J H L i j + (4 * p + D - 1)) ρ
            (truncPred j hle2 (U i (j - 1)) u s))) := by
    intro s hs v
    refine flux_le_of_gadj (I := Set.Icc t₀ t₁) (K := coarseSlot k J H L i j)
      (m' := 4 * p + D - 1) (Kc := cellKc k J H L p D i j) le_rfl i j
      (truncPred i hle1 (U (i - 1) j)) (truncPred j hle2 (U i (j - 1)))
      (fun _ s ψ x => -(AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s
        (AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p ψ) x))
      (fun v u s ψ => AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (fun x =>
        ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D, AVRegularity.wordAdjoint (d.1 - 1)
          (fun y => ContinuousLinearMap.adjoint (CE r v u d s y)
            (AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p ψ y)) x))
      (fun v s hs => diagGAdj P (h v) hKc1 hs) (fun v u s hs => edgeGAdj P hKcN v u hs)
      (G i j) ?_ hs v
    intro s hs v ψ hψ hp
    rw [predV_eq_of_tval i (U (i - 1) j) _ (fun hn => tval_truncPred hle1 _ hn),
      predV_eq_of_tval j (U i (j - 1)) _ (fun hn => tval_truncPred hle2 _ hn)]
    exact responseFlux_component hflux hs v ψ hψ hp
  -- the gradient comparisons
  have hwD : ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)), ∀ v,
      gradNormSq (K := coarseSlot k J H L i j + (4 * p + D - 1)) ρ
        (truncPred i hle1 (U (i - 1) j) v s) ≤ gradFactorialNormSq ρ (Uw (i - 1) j v s).val := by
    filter_upwards [ae_all_iff.2 hsolD.2.2.1] with s hs v
    exact gradNormSq_truncPred_le (K := coarseSlot k J H L i j + (4 * p + D - 1)) hle1 ρ
      (U (i - 1) j) (Uw (i - 1) j) v (fun _ => hs v)
  have hwE : ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)), ∀ u,
      gradNormSq (K := coarseSlot k J H L i j + (4 * p + D - 1)) ρ
        (truncPred j hle2 (U i (j - 1)) u s) ≤ gradFactorialNormSq ρ (Uw i (j - 1) u s).val := by
    filter_upwards [ae_all_iff.2 hsolE.2.2.1] with s hs u
    exact gradNormSq_truncPred_le (K := coarseSlot k J H L i j + (4 * p + D - 1)) hle2 ρ
      (U i (j - 1)) (Uw i (j - 1)) u (fun _ => hs u)
  have hcE : ∀ v u, 0 ≤ cellCgE ρ (cellKc k J H L p D i j) D H p t₀ t₁ CE v u := fun v u =>
    mul_nonneg (gfbE_nonneg _ _ _ _) (Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun d _ =>
      div_nonneg (Finset.sum_nonneg fun l _ => mul_nonneg (by positivity)
        (edgeSup_nonneg v u r d.1 l)) (by positivity))
  -- the integrated letter bound
  have hΦ := flux_mass_integral_le π P.mass_pos i j
    (cellCgE ρ (cellKc k J H L p D i j) D H p t₀ t₁ CE) hcE
    (edge_row_le P hKcN hC hΘ) (edge_col_le P hKcN hC hΘ)
    (fun s v => factorialNormSq ρ (G i j v s).val)
    (fun s v => gradNormSq (K := coarseSlot k J H L i j + (4 * p + D - 1)) ρ
      (truncPred i hle1 (U (i - 1) j) v s))
    (fun s u => gradNormSq (K := coarseSlot k J H L i j + (4 * p + D - 1)) ρ
      (truncPred j hle2 (U i (j - 1)) u s))
    (fun s v => gradFactorialNormSq ρ (Uw (i - 1) j v s).val)
    (fun s u => gradFactorialNormSq ρ (Uw i (j - 1) u s).val)
    (fun _ _ => factorialNormSq_nonneg _ _) (fun _ _ => gradNormSq_nonneg _ _)
    (fun _ _ => gradNormSq_nonneg _ _) hpt hwD hwE
    (fun v => integrable_factorialNormSq_torus (hGm v))
    (fun v => integrable_gradFactorialNormSq_torus (hsolD.2.1 v))
    (fun u => integrable_gradFactorialNormSq_torus (hsolE.2.1 u)) measurableSet_Icc
  -- the letter step
  have hS : 0 ≤ edgeS (cellKc k J H L p D i j) D H p B Cstar Θ :=
    mul_nonneg (mul_nonneg (gfbE_nonneg _ _ _ _) hB.le)
      (Finset.sum_nonneg fun r _ => pow_nonneg (mul_nonneg hC hΘ) r)
  have hstep := letter_step hB
    (Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (P.mass_pos v).le)
      (factorialNormSq_nonneg ρ (f₀ v).val))
    (integral_nonneg fun s => Finset.sum_nonneg fun v _ =>
      mul_nonneg (inv_nonneg.2 (P.mass_pos v).le) (gradFactorialNormSq_nonneg ρ _))
    (integral_nonneg fun s => Finset.sum_nonneg fun u _ =>
      mul_nonneg (inv_nonneg.2 (P.mass_pos u).le) (gradFactorialNormSq_nonneg ρ _))
    (cellCgD_nonneg P hσ _) hS i j hE0 hΦ
    (fun _ => grad_le_strongEnergy_sq hB.le P.mass_pos (U (i - 1) j) (Uw (i - 1) j) hsolD.2.1)
    (fun _ => grad_le_strongEnergy_sq hB.le P.mass_pos (U i (j - 1)) (Uw i (j - 1)) hsolE.2.1)
  refine hstep.trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
    (initial_mass_le (by omega) f f₀ i j hf₀ π P.mass_pos ρ)) (Real.sqrt_nonneg _))
end

/-! **The binomial word energy bound**: with the letter sizes
`q₀ = C(a B₀ ‖H_cov‖_∞/B + ∑_d 𝒜_{ρ,N}(A_d)/(Bρ^{d-2}))` and `q₁ = C ∑_{r=1}^H (C_*Θ)^r`, the strong
energy of the cell `(i,j)` of every coarse response family is at most
`4 binom(i+j,i) (4q₀)^i (4q₁)^j |f|_{ρ,N;π}`. The constant `C` depends only on `D, H, p, J, k`:
it dominates the gradient constants of the response operators at every order through
`N = k + (J+H+3)(D+8p+4)`. -/

section
/-- The constant of the word energy bound. -/
def wordConst (D H p J k : ℕ) : ℝ :=
  7 * ∑ Kc ∈ Finset.range (k + (J + H + 3) * (D + 8 * p + 4) + 1),
    (gfbD Kc D p + gfbE Kc D H p)

theorem wordConst_nonneg (D H p J k : ℕ) : 0 ≤ wordConst D H p J k :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun Kc _ =>
    add_nonneg (gfbD_nonneg Kc D p) (gfbE_nonneg Kc D H p))

theorem gfbD_le_wordConst {D H p J k Kc : ℕ} (hKc : Kc ≤ k + (J + H + 3) * (D + 8 * p + 4)) :
    7 * gfbD Kc D p ≤ wordConst D H p J k := by
  unfold wordConst
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine le_trans ?_ (Finset.single_le_sum (f := fun Kc => gfbD Kc D p + gfbE Kc D H p)
    (fun Kc _ => add_nonneg (gfbD_nonneg Kc D p) (gfbE_nonneg Kc D H p))
    (Finset.mem_range.2 (by omega : Kc < k + (J + H + 3) * (D + 8 * p + 4) + 1)))
  exact le_add_of_nonneg_right (gfbE_nonneg Kc D H p)

theorem gfbE_le_wordConst {D H p J k Kc : ℕ} (hKc : Kc ≤ k + (J + H + 3) * (D + 8 * p + 4)) :
    7 * gfbE Kc D H p ≤ wordConst D H p J k := by
  unfold wordConst
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine le_trans ?_ (Finset.single_le_sum (f := fun Kc => gfbD Kc D p + gfbE Kc D H p)
    (fun Kc _ => add_nonneg (gfbD_nonneg Kc D p) (gfbE_nonneg Kc D H p))
    (Finset.mem_range.2 (by omega : Kc < k + (J + H + 3) * (D + 8 * p + 4) + 1)))
  exact le_add_of_nonneg_left (gfbD_nonneg Kc D p)

theorem sqrt_6_le : Real.sqrt 6 ≤ 4 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

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

/-- **The binomial word energy bound.** -/
theorem word_energy
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    (hC : 0 ≤ Cstar) (hΘ : 0 ≤ Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {q₀ q₁ : ℝ}
    (hq₀ : q₀ = wordConst D H p J k *
      (a * B₀ * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
        + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
            (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal))
    (hq₁ : q₁ = wordConst D H p J k * (∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r))
    {i j : ℕ} (hi : i ≤ J) (hj : j ≤ H) :
    strongEnergy ρ B π t₀ t₁ (U i j) (Uw i j)
      ≤ ENNReal.ofReal (4 * (Nat.choose (i + j) i : ℝ) * (4 * q₀) ^ i * (4 * q₁) ^ j *
        Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π (fun v => (f v).val))) := by
  have hB := P.B_pos
  have hσ : 0 ≤ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal := ENNReal.toReal_nonneg
  have hC0 := wordConst_nonneg D H p J k
  have hY₀ : 0 ≤ a * B₀ * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / B
      + (∑ d : Finset.Icc 2 D, coefficientSeminorm ρ N t₀ t₁ (AD d) *
          (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹).toReal := by
    have := P.a_nonneg
    have : 0 ≤ B₀ := zero_le_one.trans P.B₀_ge
    exact add_nonneg (div_nonneg (by positivity) hB.le) ENNReal.toReal_nonneg
  have hsumr : 0 ≤ ∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r :=
    Finset.sum_nonneg fun r _ => pow_nonneg (mul_nonneg hC hΘ) r
  have hq₀0 : 0 ≤ q₀ := hq₀ ▸ mul_nonneg hC0 hY₀
  have hq₁0 : 0 ≤ q₁ := hq₁ ▸ mul_nonneg hC0 hsumr
  refine binomial_word_bound (x := 4 * q₀) (y := 4 * q₁) (by positivity) (by positivity)
    (Real.sqrt_nonneg _) (fun i j => strongEnergy ρ B π t₀ t₁ (U i j) (Uw i j)) J H ?_ i hi j hj
  intro i hi j hj
  beta_reduce
  refine (cell_step P hC hΘ hR hi hj).trans ?_
  have hKc : cellKc k J H L p D i j ≤ k + (J + H + 3) * (D + 8 * p + 4) := by
    have h1 := coarseSlot_add_le k J H L N i j P.N_eq
    have h2 : N = k + (J + H + 3) * (D + 8 * p + 4) := by rw [P.N_eq, P.L_eq]
    have := P.L_eq
    unfold cellKc
    omega
  have hKcN : cellKc k J H L p D i j ≤ N := by
    have h2 : N = k + (J + H + 3) * (D + 8 * p + 4) := by rw [P.N_eq, P.L_eq]
    omega
  refine add_le_add (add_le_add ?_ ?_) ?_
  · split_ifs with h00
    · exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right sqrt_6_le (Real.sqrt_nonneg _))
    · simp
  · split_ifs with hi0
    · exact le_rfl
    · refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
      have h1 := letterD_le P hσ hKcN
      have h2 := gfbD_le_wordConst (H := H) hKc
      rw [hq₀]
      refine h1.trans ?_
      nlinarith
  · split_ifs with hj0
    · exact le_rfl
    · refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
      have h2 := gfbE_le_wordConst (H := H) hKc
      have hg := gfbE_nonneg (cellKc k J H L p D i j) D H p
      have e : Real.sqrt 48 * edgeS (cellKc k J H L p D i j) D H p B Cstar Θ / B =
          Real.sqrt 48 * gfbE (cellKc k J H L p D i j) D H p *
            ∑ r ∈ Finset.Icc 1 H, (Cstar * Θ) ^ r := by
        unfold edgeS
        field_simp
      rw [e, hq₁]
      have h3 : Real.sqrt 48 * gfbE (cellKc k J H L p D i j) D H p ≤
          7 * gfbE (cellKc k J H L p D i j) D H p :=
        mul_le_mul_of_nonneg_right sqrt_48_le hg
      have h4 := mul_le_mul_of_nonneg_right h3 hsumr
      nlinarith
end

end AVRegularity.CycleComparison.Coarse
end
