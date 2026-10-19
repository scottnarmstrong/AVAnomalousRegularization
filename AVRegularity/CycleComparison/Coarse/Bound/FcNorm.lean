-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Coarse.Energy.Word
import AVRegularity.CycleComparison.Coarse.Energy.Zero
public import AVRegularity.CycleComparison.Coarse.Defect.ConjW
public import AVRegularity.CycleComparison.Coarse.Bound.AtTime
import AVRegularity.CoupledEnergy.Variational.DriftCarrierBudget
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! Support of the coarse responses on the acyclic edge graph: a graded response `U_{i,j,v}` vanishes
on the window unless the graded depth `j` is reachable by a walk of the edge matrix ending at `v`
(i.e. a walk `v ↝ w` of length at least `j`). In particular the depth `H + 1` is never reachable, and
the terminal edge pairing of the top-depth responses vanishes. -/

section Reach

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Some walk of length at least `j` starts at `u` (with nonzero weight). -/
def edgeReach (A : Matrix ι ι ℝ) (j : ℕ) (u : ι) : Prop :=
  ∃ m, j ≤ m ∧ ∃ w, (A ^ m) u w ≠ 0

theorem edgeReach_zero (A : Matrix ι ι ℝ) (u : ι) : edgeReach A 0 u :=
  ⟨0, le_rfl, u, by simp⟩

theorem edgeReach_mono {A : Matrix ι ι ℝ} {j j' : ℕ} {u : ι} (hj : j' ≤ j)
    (h : edgeReach A j u) : edgeReach A j' u := by
  obtain ⟨m, hm, w, hw⟩ := h
  exact ⟨m, hj.trans hm, w, hw⟩

theorem matrix_pow_nonneg' {A : Matrix ι ι ℝ} (hA : ∀ v u, 0 ≤ A v u) :
    ∀ (m : ℕ) (v u : ι), 0 ≤ (A ^ m) v u
  | 0, v, u => by
      rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | m + 1, v, u => by
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun x _ => mul_nonneg (matrix_pow_nonneg' hA m v x) (hA x u)

theorem edgeReach_step {A : Matrix ι ι ℝ} (hA : ∀ v u, 0 ≤ A v u) {r j : ℕ} {v u : ι}
    (hr : (A ^ r) v u ≠ 0) (hu : edgeReach A j u) : edgeReach A (r + j) v := by
  obtain ⟨m, hm, w, hw⟩ := hu
  refine ⟨r + m, Nat.add_le_add_left hm r, w, ?_⟩
  rw [pow_add, Matrix.mul_apply]
  have hpos : 0 < (A ^ r) v u * (A ^ m) u w :=
    mul_pos (lt_of_le_of_ne (matrix_pow_nonneg' hA r v u) (Ne.symm hr))
      (lt_of_le_of_ne (matrix_pow_nonneg' hA m u w) (Ne.symm hw))
  exact (lt_of_lt_of_le hpos (Finset.single_le_sum
    (f := fun x => (A ^ r) v x * (A ^ m) x w)
    (fun x _ => mul_nonneg (matrix_pow_nonneg' hA r v x) (matrix_pow_nonneg' hA m x w))
    (Finset.mem_univ u))).ne'

theorem not_edgeReach_of_acyclic {A : Matrix ι ι ℝ} {H : ℕ} (h : A ^ (H + 1) = 0) (u : ι) :
    ¬ edgeReach A (H + 1) u := by
  rintro ⟨m, hm, w, hw⟩
  apply hw
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, h, zero_mul]
  rfl

end Reach

section Coeff

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

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
/-- A zero entry of the edge matrix power kills the corresponding coefficient. -/
theorem edge_coeff_eq_zero
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {r : ℕ} (hr : r ∈ Finset.Icc 1 H) {v u : ι} (h0 : (Aedge ^ r) v u = 0)
    (d : Finset.Icc 2 D) {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (x : Vec 2) :
    CE r v u d s x = 0 := by
  have hm := P.edge_mean r hr v u
  rw [h0, mul_zero, ENNReal.ofReal_zero] at hm
  have hpos : ENNReal.ofReal (Real.sqrt (π u / π v)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 (div_pos (P.mass_pos u) (P.mass_pos v)))).ne'
  have hsum := (mul_eq_zero.1 (le_zero_iff.1 hm)).resolve_left hpos
  have hd := (Finset.sum_eq_zero_iff.1 hsum) d (Finset.mem_univ d)
  have hsem : coefficientSeminorm ρ N t₀ t₁ (CE r v u d) = 0 := by
    refine (mul_eq_zero.1 hd).resolve_right ?_
    intro hinv
    exact ENNReal.ofReal_ne_top (ENNReal.inv_eq_zero.1 hinv)
  have hterm := coeffSup_term_le (ρ := ρ) (t₀ := t₀) (t₁ := t₁) (CE r v u d) (Nat.zero_le N)
  rw [hsem] at hterm
  have hS : (⨆ t ∈ Set.Icc t₀ t₁, ⨆ x : Vec 2,
      (‖coefficientDerivativeArray (CE r v u d t) 0 x‖₊ : ENNReal)) = 0 := by
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one,
      one_mul, nonpos_iff_eq_zero] at hterm
    exact hterm
  have h1 : (‖coefficientDerivativeArray (CE r v u d s) 0 x‖₊ : ENNReal) ≤ 0 := by
    rw [← hS]
    exact le_iSup₂_of_le s hs (le_iSup_of_le x le_rfl)
  have h2 : ‖coefficientDerivativeArray (CE r v u d s) 0 x‖ = 0 := by
    have := nonpos_iff_eq_zero.1 h1
    have h3 : ‖coefficientDerivativeArray (CE r v u d s) 0 x‖₊ = 0 := by simpa using this
    exact congrArg ((↑) : NNReal → ℝ) h3
  rw [AVRegularity.CoupledEnergy.Variational.coefficientDerivativeArray_zero_norm] at h2
  exact norm_eq_zero.1 h2

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- The edge block vanishes when all the edge entries into it vanish. -/
theorem edgeBlock_eq_zero_of_not_reach
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {v u : ι} (h0 : ∀ r ∈ Finset.Icc 1 H, (Aedge ^ r) v u = 0) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) (χ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) :
    edgeBlock D H CE s v u χ = 0 := by
  funext x
  unfold edgeBlock
  refine Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun d _ => ?_
  have hz : (fun y => ContinuousLinearMap.adjoint (CE r v u d s y) (χ y)) =
      fun _ => (0 : PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) := by
    funext y
    rw [edge_coeff_eq_zero P hr (h0 r hr) d hs y]
    simp
  rw [hz, wordAdjoint_zero_field]

end Coeff

section Support

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A periodic Sobolev field with vanishing factorial norm at a positive radius is zero. -/
theorem torusHk_eq_zero_of_factorialNormSq_le {K : ℕ} {ρ : ℝ} {X : TorusHk K E}
    (hX : factorialNormSq ρ X.val ≤ 0) : X = 0 := by
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin (K + 1))),
      0 ≤ factorialWeight ρ j.val * derivativeNormSq X.val j := fun j _ =>
    mul_nonneg (factorialWeight_nonneg ρ _) (derivativeNormSq_nonneg _ _)
  have hsum : ∑ j : Fin (K + 1), factorialWeight ρ j.val * derivativeNormSq X.val j = 0 :=
    le_antisymm hX (Finset.sum_nonneg hnn)
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum ⟨0, Nat.succ_pos K⟩
    (Finset.mem_univ _)
  have hw : 0 < factorialWeight ρ 0 := by
    unfold factorialWeight
    simp
  have hd : derivativeNormSq X.val ⟨0, Nat.succ_pos K⟩ = 0 :=
    (mul_eq_zero.1 h0).resolve_left hw.ne'
  unfold derivativeNormSq at hd
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 hd
    (Fin.elim0 : Fin 0 → Fin 2) (Finset.mem_univ _)
  apply TorusHk.ext_value
  have h2 : X.val (valueIndex2 K) = 0 := norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 h1)
  rw [h2]
  rfl

omit [FiniteDimensional ℝ E] in
theorem cellInner_jet_zero {K : ℕ} {X : TorusHk K E} (hX : X = 0) (ψ : Vec 2 → E) :
    cellInner (fun x => X.toFunction.jet (valueIndex2 K) x) ψ = 0 := by
  subst hX
  exact cellInner_tval_zero ψ

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

/-- **Support of the graded responses.** A response of depth `j` at a vertex from which no walk of
length `j` starts vanishes on the window. -/
theorem response_eq_zero_of_not_reach
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G) :
    ∀ j ≤ H, ∀ i ≤ J, ∀ v, ¬ edgeReach Aedge j v → ∀ s ∈ Set.Icc t₀ t₁, U i j v s = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hjH i
  induction i using Nat.strong_induction_on with
  | _ i ihi =>
  intro hiJ v hv
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact absurd (edgeReach_zero _ v) hv
  obtain ⟨f₀, hf0, hsol, hflux⟩ := hR i hiJ j hjH
  have hf0' : ∀ w, f₀ w = 0 := by
    have hn : ¬ (i = 0 ∧ j = 0) := fun hh => by omega
    simpa [hn] using hf0
  have key : ∀ x y : ℝ, x = 0 → y = 0 → x + y = 0 := fun x y hx hy => by rw [hx, hy, add_zero]
  have hedge : ∀ s ∈ Set.Icc t₀ t₁, ∀ (u : ι) (χ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)),
      cellInner (fun x => (U i (j - 1) u s).toFunction.jet
          (valueIndex2 (coarseSlot k J H L i (j - 1))) x)
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
          (fun x => ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D, wordAdjoint (d.1 - 1)
            (fun y => ContinuousLinearMap.adjoint (CE r v u d s y) (χ y)) x)) = 0 := by
    intro s hs u χ
    by_cases hu : edgeReach Aedge (j - 1) u
    · have h0 : ∀ r ∈ Finset.Icc 1 H, (Aedge ^ r) v u = 0 := by
        intro r hr
        by_contra hne
        exact hv (edgeReach_mono (by have := (Finset.mem_Icc.1 hr).1; omega)
          (edgeReach_step P.edge_nonneg hne hu))
      have hb := edgeBlock_eq_zero_of_not_reach P h0 hs χ
      have hb' : (fun x => ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D, wordAdjoint (d.1 - 1)
            (fun y => ContinuousLinearMap.adjoint (CE r v u d s y) (χ y)) x) = 0 := hb
      rw [hb', covPolyP_zero_field]
      simp [cellInner]
    · exact cellInner_jet_zero (ih (j - 1) (by omega) (by omega) i hiJ u hu s hs) _
  have hGz : ∀ s ∈ Set.Icc t₀ t₁, G i j v s = 0 := by
    intro s hs
    apply torusHk_eq_of_cellInner
    intro ψ hψ hper
    rw [cellInner_tval_zero]
    have hc := responseFlux_component hflux hs v ψ hψ hper
    have hj0 : j ≠ 0 := by omega
    refine hc.trans ?_
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · simp only [hi0, hj0, ↓reduceIte]
      refine key _ _ ?_ (Finset.sum_eq_zero fun u _ => hedge s hs u _)
      simp [cellInner]
    · have hi0' : i ≠ 0 := by omega
      simp only [hi0', hj0, ↓reduceIte]
      exact key _ _ (cellInner_jet_zero (ihi (i - 1) (by omega) (by omega) v hv s hs) _)
        (Finset.sum_eq_zero fun u _ => hedge s hs u _)
  intro s hs
  have hE := response_component_le P (coarseSlot_le_input k J H L N i j P.N_eq) (f₀ := f₀)
    (G := G i j) (fun w => coarseResponses_flux_memLp P hR hiJ hjH w) hsol v hs
  have hf : factorialNormSq ρ (f₀ v).val = 0 := by
    rw [hf0' v]
    simp [factorialNormSq, derivativeNormSq]
  have hI : (∫ s' in Set.Icc t₀ t₁, (π v)⁻¹ * factorialNormSq ρ (G i j v s').val) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (0 : ℝ)) (fun s' hs' => by
      simp only [hGz s' hs']
      simp [factorialNormSq, derivativeNormSq])]
    simp
  have hnn : 0 ≤ B / 2 * ∫ s' in Set.Icc t₀ t₁,
      (π v)⁻¹ * gradFactorialNormSq ρ (Uw i j v s').val :=
    mul_nonneg (by have := P.B_pos; positivity) (setIntegral_nonneg measurableSet_Icc
      (fun s' _ => mul_nonneg (inv_nonneg.2 (P.mass_pos v).le) (gradFactorialNormSq_nonneg _ _)))
  rw [hf, hI] at hE
  have hle : (π v)⁻¹ * factorialNormSq ρ (U i j v s).val ≤ 0 := by linarith
  have hx : factorialNormSq ρ (U i j v s).val ≤ 0 :=
    le_of_mul_le_mul_left (by rw [mul_zero]; exact hle) (inv_pos.2 (P.mass_pos v))
  exact torusHk_eq_zero_of_factorialNormSq_le hx

/-- **Terminal edge vanishing.** The pairing of the top-depth responses with the edge block into
the vertex `v` from `u` vanishes. -/
theorem terminal_edge_pairing_eq_zero
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v u : ι)
    (χ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) :
    cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ {H}) u s)
      (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (edgeBlock D H CE s v u χ)) = 0 := by
  by_cases hu : edgeReach Aedge H u
  · have h0 : ∀ r ∈ Finset.Icc 1 H, (Aedge ^ r) v u = 0 := by
      intro r hr
      by_contra hne
      exact not_edgeReach_of_acyclic P.edge_acyclic v (edgeReach_mono
        (by have := (Finset.mem_Icc.1 hr).1; omega) (edgeReach_step P.edge_nonneg hne hu))
    rw [edgeBlock_eq_zero_of_not_reach P h0 hs χ, covPolyP_zero_field]
    simp [cellInner]
  · have hz : ∀ ij ∈ Finset.range (J + 1) ×ˢ ({H} : Finset ℕ),
        ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
          (U ij.1 ij.2 u s).toFunction.jet (valueIndex2 (coarseSlot k J H L ij.1 ij.2)) x = 0 := by
      intro ij hij
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hij
      have hi : ij.1 ≤ J := Nat.lt_succ_iff.1 (Finset.mem_range.1 h1)
      have hj : ij.2 = H := Finset.mem_singleton.1 h2
      have hU := response_eq_zero_of_not_reach P hR ij.2 hj.le ij.1 hi u (hj ▸ hu) s hs
      rw [hU]
      exact tval_zero_ae
    have hae : familyValueSum k J H L U (Finset.range (J + 1) ×ˢ {H}) u s
        =ᵐ[volume.restrict AVenhance.unitCube] fun _ => 0 := by
      filter_upwards [(Filter.eventually_all_finset _).2 hz] with x hx
      exact Finset.sum_eq_zero hx
    rw [cellInner_congr_left hae]
    simp [cellInner]

end Support

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! **The energy of the retained field.** On the window the retained field `W` is `𝖯_p(t)^*`
applied to the truncated sum of the responses; its value part is bounded by the factorial
bound of `𝖯_p^*`, and its gradient is `𝖯_p^*` applied to the gradient of the truncated sum
(`∂_j` commutes with `𝖯_p`). Cauchy–Schwarz over the cells of the box gives the energy bound
`strongEnergyUpTo W ≤ κ √#box ∑_{ij} strongEnergy (U_ij)`. -/

section Abs

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] {μ : Measure (Vec 2)}

theorem factorialNormSqUpTo_le_factorialNormSq {K : ℕ} (ρ : ℝ) (m : ℕ) (D : JetL2 μ K E) :
    factorialNormSqUpTo ρ m D ≤ factorialNormSq ρ D := by
  unfold factorialNormSqUpTo factorialNormSq
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (factorialWeight_nonneg ρ _) (derivativeNormSq_nonneg D j)

theorem gradFactorialNormSqUpTo_le_gradFactorialNormSq {K : ℕ} (ρ : ℝ) (m : ℕ)
    (D : JetL2 μ (K + 1) E) :
    gradFactorialNormSqUpTo ρ m D ≤ gradFactorialNormSq ρ D := by
  unfold gradFactorialNormSqUpTo gradFactorialNormSq
  rw [Fin.sum_univ_succ]
  have h0 : (if 1 ≤ (0 : Fin (K + 1 + 1)).val ∧ (0 : Fin (K + 1 + 1)).val ≤ m + 1 then
      factorialWeight ρ ((0 : Fin (K + 1 + 1)).val - 1) * derivativeNormSq D 0 else 0) = 0 :=
    by simp
  rw [h0, zero_add]
  refine Finset.sum_le_sum fun l _ => ?_
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (factorialWeight_nonneg ρ _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end Abs

section AbsTorus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

theorem gradFactorialNormSqUpTo_torusCast {K L : ℕ} (ρ : ℝ) (m : ℕ) (h : K = L)
    (U : TorusHk K E) :
    gradFactorialNormSqUpTo ρ m (torusCast h U).val = gradFactorialNormSqUpTo ρ m U.val := by
  subst h; rfl

theorem gradNormSq_eq_gradFactorialNormSq {K : ℕ} (ρ : ℝ) (U : TorusHk (K + 1) E) :
    gradNormSq (K := K) ρ U = gradFactorialNormSq ρ U.val :=
  (gradNormSq_eq ρ U).trans (gradFactorialNormSq_eq ρ U.val).symm

theorem gradNormSq_sum_le {ι : Type*} (s : Finset ι) {K : ℕ} (ρ : ℝ)
    (Z : ι → TorusHk (K + 1) E) :
    gradNormSq (K := K) ρ (∑ i ∈ s, Z i) ≤
      (s.card : ℝ) * ∑ i ∈ s, gradNormSq (K := K) ρ (Z i) := by
  unfold gradNormSq
  have hj : ∀ j : Fin 2, factorialNormSq ρ
      (derivativeTorusHk (E := E) (K := K) (r := 1) (fun _ => j) (∑ i ∈ s, Z i)).val ≤
      (s.card : ℝ) * ∑ i ∈ s, factorialNormSq ρ
        (derivativeTorusHk (E := E) (K := K) (r := 1) (fun _ => j) (Z i)).val := by
    intro j
    rw [map_sum]
    have h1 := sqrt_fNSq_torus_sum_le ρ s
      (fun i => derivativeTorusHk (E := E) (K := K) (r := 1) (fun _ => j) (Z i))
    have h2 := sq_sum_le_card_mul_sum_sq (s := s)
      (f := fun i => Real.sqrt (factorialNormSq ρ
        (derivativeTorusHk (E := E) (K := K) (r := 1) (fun _ => j) (Z i)).val))
    calc _ = (Real.sqrt (factorialNormSq ρ
          (∑ i ∈ s, derivativeTorusHk (E := E) (K := K) (r := 1) (fun _ => j) (Z i)).val)) ^ 2 :=
          (Real.sq_sqrt (factorialNormSq_nonneg _ _)).symm
      _ ≤ (∑ i ∈ s, Real.sqrt (factorialNormSq ρ
          (derivativeTorusHk (E := E) (K := K) (r := 1) (fun _ => j) (Z i)).val)) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      _ ≤ _ := h2
      _ = _ := by
          congr 1
          exact Finset.sum_congr rfl fun i _ => Real.sq_sqrt (factorialNormSq_nonneg _ _)
  calc _ ≤ ∑ j : Fin 2, (s.card : ℝ) * ∑ i ∈ s, factorialNormSq ρ
        (derivativeTorusHk (E := E) (K := K) (r := 1) (fun _ => j) (Z i)).val :=
        Finset.sum_le_sum fun j _ => hj j
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end AbsTorus

section Ident

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- **The gradient of the retained field is `𝖯_p^*` applied to the gradient of the sum.** -/
theorem derivative_retained_eq {k D p L : ℕ} (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (hord : k + 1 + D + 2 * p ≤ k + 2 * L)
    (Wt : TorusHk (k + 1 + D) E) (Rs : TorusHk (k + 2 * L) E) (V : Vec 2 → E)
    (hW : ∀ χ : Vec 2 → E, ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) χ →
      AVenhance.IsZ2Periodic χ →
      cellInner (tval Wt) χ = cellInner V (AVRegularity.covPolyP Hc p χ))
    (hR : ∀ φ : Vec 2 → E, Continuous φ → cellInner (tval Rs) φ = cellInner V φ) (j : Fin 2) :
    derivativeTorusHk (K := k + D) (r := 1) (fun _ => j)
        (torusCast (by omega : k + 1 + D = k + D + 1) Wt) =
      (TorusAdj.covPolyP (E := E) Hc le_rfl p 0 (k + 2 * L)).adj (k + D) (by omega)
        (derivativeTorusHk (K := k + D + 2 * p) (r := 1) (fun _ => j)
          (truncateTorusHk (by omega : k + D + 2 * p + 1 ≤ k + 2 * L) Rs)) := by
  refine torusHk_eq_of_cellInner fun ψ hψ hp => ?_
  have hψn : ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) ψ := fun n =>
    hψ.of_le (by exact_mod_cast le_top)
  have hcomm := (ConstCoefOp.covPolyP (E := E) Hc p).comm j ψ (hψn _)
  have hPψ : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (AVRegularity.covPolyP Hc p ψ) :=
    (ConstCoefOp.covPolyP (E := E) Hc p).reg 1 ψ (hψn _)
  have hPp : AVenhance.IsZ2Periodic (AVRegularity.covPolyP Hc p ψ) :=
    isZ2Periodic_covPolyP Hc p hψ hp
  have hdψ := (TorusAdj.coordDeriv (E := E) j (2 * p) 0).maps (2 * p) le_rfl ψ (hψn _) hp
  have hcont : Continuous (fun x => fderiv ℝ (AVRegularity.covPolyP Hc p ψ) x (basisVec j)) :=
    (hPψ.continuous_fderiv (by simp)).clm_apply continuous_const
  -- left side
  have hL : cellInner (tval (derivativeTorusHk (E := E) (K := k + D) (r := 1) (fun _ => j)
        (torusCast (by omega : k + 1 + D = k + D + 1) Wt))) ψ =
      -cellInner V (AVRegularity.covPolyP Hc p (partialOp j ψ)) := by
    rw [tval_derivativeTorusHk_single,
      cellInner_firstDerivative_eq_neg _ j (hψn 1) hp, tval_torusCast]
    exact congrArg Neg.neg (hW _ hdψ.1 hdψ.2)
  have hR' : cellInner (tval (derivativeTorusHk (E := E) (K := k + D + 2 * p) (r := 1) (fun _ => j)
          (truncateTorusHk (by omega : k + D + 2 * p + 1 ≤ k + 2 * L) Rs))) 
        (AVRegularity.covPolyP Hc p ψ) =
      -cellInner V (partialOp j (AVRegularity.covPolyP Hc p ψ)) := by
    rw [tval_derivativeTorusHk_single,
      cellInner_firstDerivative_eq_neg _ j hPψ hPp, tval_truncateTorusHk]
    exact congrArg Neg.neg (hR _ hcont)
  rw [hL, (TorusAdj.covPolyP (E := E) Hc le_rfl p 0 (k + 2 * L)).ident _ _ _ ψ (hψn _) hp,
    hR', hcomm]

/-- **The gradient factorial norm of the retained field.** -/
theorem gradUpTo_retained_le {k D p L : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (hord : k + 1 + D + 2 * p ≤ k + 2 * L)
    (Wt : TorusHk (k + 1 + D) E) (Rs : TorusHk (k + 2 * L) E) (V : Vec 2 → E)
    (hW : ∀ χ : Vec 2 → E, ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) χ →
      AVenhance.IsZ2Periodic χ →
      cellInner (tval Wt) χ = cellInner V (AVRegularity.covPolyP Hc p χ))
    (hR : ∀ φ : Vec 2 → E, Continuous φ → cellInner (tval Rs) φ = cellInner V φ)
    {ι : Type*} (S : Finset ι) (Z : ι → TorusHk (k + D + 2 * p + 1) E)
    (hZ : truncateTorusHk (by omega : k + D + 2 * p + 1 ≤ k + 2 * L) Rs = ∑ i ∈ S, Z i) :
    gradFactorialNormSqUpTo ρ k Wt.val ≤
      covPolyConst (fbCovConst ρ Hc (k + 2 * L)) p ^ 2 *
        ((S.card : ℝ) * ∑ i ∈ S, gradNormSq (K := k + D + 2 * p) ρ (Z i)) := by
  set Cf := covPolyConst (fbCovConst ρ Hc (k + 2 * L)) p with hCf
  set Wc := torusCast (by omega : k + 1 + D = k + D + 1) Wt with hWc
  set R2 := truncateTorusHk (by omega : k + D + 2 * p + 1 ≤ k + 2 * L) Rs with hR2
  have h1 : gradFactorialNormSqUpTo ρ k Wt.val ≤ gradNormSq (K := k + D) ρ Wc :=
    calc _ = gradFactorialNormSqUpTo ρ k Wc.val :=
          (gradFactorialNormSqUpTo_torusCast ρ k _ Wt).symm
      _ ≤ gradFactorialNormSq ρ Wc.val := gradFactorialNormSqUpTo_le_gradFactorialNormSq ρ k _
      _ = _ := (gradNormSq_eq_gradFactorialNormSq ρ Wc).symm
  have hj : ∀ j : Fin 2, factorialNormSq ρ
      (derivativeTorusHk (E := E) (K := k + D) (r := 1) (fun _ => j) Wc).val ≤
      Cf ^ 2 * factorialNormSq ρ
        (derivativeTorusHk (E := E) (K := k + D + 2 * p) (r := 1) (fun _ => j) R2).val := by
    intro j
    rw [hWc, derivative_retained_eq Hc hord Wt Rs V hW hR j]
    have hb := (TorusAdj.FBound.covPolyP (E := E) hρ Hc le_rfl p 0 (k + 2 * L)) (k + D)
      (by omega) (derivativeTorusHk (E := E) (K := k + D + 2 * p) (r := 1) (fun _ => j) R2)
    calc _ = (Real.sqrt (factorialNormSq ρ ((TorusAdj.covPolyP (E := E) Hc le_rfl p 0
            (k + 2 * L)).adj (k + D) (by omega) (derivativeTorusHk (E := E) (K := k + D + 2 * p)
              (r := 1) (fun _ => j) R2)).val)) ^ 2 :=
          (Real.sq_sqrt (factorialNormSq_nonneg _ _)).symm
      _ ≤ (Cf * Real.sqrt (factorialNormSq ρ
            (derivativeTorusHk (E := E) (K := k + D + 2 * p) (r := 1) (fun _ => j) R2).val)) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt (factorialNormSq_nonneg _ _)]
  have h2 : gradNormSq (K := k + D) ρ Wc ≤ Cf ^ 2 * gradNormSq (K := k + D + 2 * p) ρ R2 := by
    unfold gradNormSq
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hj j
  have h3 : gradNormSq (K := k + D + 2 * p) ρ R2 ≤
      (S.card : ℝ) * ∑ i ∈ S, gradNormSq (K := k + D + 2 * p) ρ (Z i) := by
    rw [hZ]
    exact gradNormSq_sum_le S ρ Z
  exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _)))

end Ident

section Assembly

theorem rpow_half_sum_le {κ : Type*} (s : Finset κ) (a : κ → ℝ≥0∞) :
    (∑ i ∈ s, a i) ^ (1 / 2 : ℝ) ≤ ∑ i ∈ s, a i ^ (1 / 2 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans
      (add_le_add le_rfl ih)

/-- **ENNReal assembly of the energy bound** (abstract real form). -/
theorem energy_assembly {ι κ : Type*} [Fintype ι] (cells : Finset κ) (π : ι → ℝ)
    (B t₀ t₁ C : ℝ) (hC : 0 ≤ C) (a g : ι → ℝ → ℝ) (x y : κ → ι → ℝ → ℝ)
    (hx : ∀ ij v t, 0 ≤ x ij v t) (hy0 : ∀ ij v s, 0 ≤ y ij v s)
    (hym : ∀ ij ∈ cells, ∀ v, AEMeasurable (y ij v) (volume.restrict (Set.Icc t₀ t₁)))
    (hval : ∀ v, ∀ t ∈ Set.Icc t₀ t₁, a v t ≤ C * ∑ ij ∈ cells, x ij v t)
    (hgrad : ∀ v, ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)),
      g v s ≤ C * ∑ ij ∈ cells, y ij v s) :
    (∑ v, ENNReal.ofReal (π v)⁻¹ *
        ((⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (a v t)) +
          ENNReal.ofReal B * ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (g v s))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt C) * ∑ ij ∈ cells,
        (∑ v, ENNReal.ofReal (π v)⁻¹ *
          ((⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (x ij v t)) +
            ENNReal.ofReal B * ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (y ij v s))) ^ (1 / 2 : ℝ) := by
  set Q : κ → ι → ℝ≥0∞ := fun ij v => (⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (x ij v t)) +
    ENNReal.ofReal B * ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (y ij v s) with hQ
  have hv : ∀ v, ((⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (a v t)) +
      ENNReal.ofReal B * ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (g v s)) ≤
      ENNReal.ofReal C * ∑ ij ∈ cells, Q ij v := by
    intro v
    have h1 : (⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (a v t)) ≤ ENNReal.ofReal C *
        ∑ ij ∈ cells, ⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (x ij v t) := by
      refine iSup₂_le fun t ht => ?_
      calc ENNReal.ofReal (a v t) ≤ ENNReal.ofReal (C * ∑ ij ∈ cells, x ij v t) :=
            ENNReal.ofReal_le_ofReal (hval v t ht)
        _ = ENNReal.ofReal C * ∑ ij ∈ cells, ENNReal.ofReal (x ij v t) := by
            rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg (fun ij _ => hx ij v t)]
        _ ≤ _ := by
            refine mul_le_mul_right (Finset.sum_le_sum fun ij _ => ?_) _
            exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc t₀ t₁) => ENNReal.ofReal (x ij v t)) t ht
    have h2 : (∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (g v s)) ≤ ENNReal.ofReal C *
        ∑ ij ∈ cells, ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (y ij v s) := by
      calc (∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (g v s)) ≤
            ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal C * ∑ ij ∈ cells, ENNReal.ofReal (y ij v s) :=
            lintegral_mono_ae ((hgrad v).mono fun s hs => by
              rw [← ENNReal.ofReal_sum_of_nonneg (fun ij _ => hy0 ij v s),
                ← ENNReal.ofReal_mul hC]
              exact ENNReal.ofReal_le_ofReal hs)
        _ = _ := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_finsetSum' _ (fun ij hij => (hym ij hij v).ennreal_ofReal)]
    calc _ ≤ ENNReal.ofReal C * ∑ ij ∈ cells, (⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (x ij v t)) +
          ENNReal.ofReal B * (ENNReal.ofReal C *
            ∑ ij ∈ cells, ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (y ij v s)) :=
          add_le_add h1 (mul_le_mul_right h2 _)
      _ = ENNReal.ofReal C * (∑ ij ∈ cells, (⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (x ij v t)) +
          ENNReal.ofReal B * ∑ ij ∈ cells, ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (y ij v s)) := by
          ring
      _ = _ := by
          rw [Finset.mul_sum (s := cells), ← Finset.sum_add_distrib]
  have hsum : (∑ v, ENNReal.ofReal (π v)⁻¹ *
      ((⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (a v t)) +
        ENNReal.ofReal B * ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (g v s))) ≤
      ENNReal.ofReal C * ∑ ij ∈ cells, ∑ v, ENNReal.ofReal (π v)⁻¹ * Q ij v := by
    calc _ ≤ ∑ v, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal C * ∑ ij ∈ cells, Q ij v) :=
          Finset.sum_le_sum fun v _ => mul_le_mul_right (hv v) _
      _ = ∑ v, ENNReal.ofReal C * ∑ ij ∈ cells, ENNReal.ofReal (π v)⁻¹ * Q ij v :=
          Finset.sum_congr rfl fun v _ => by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun ij _ => by ring
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  refine (ENNReal.rpow_le_rpow hsum (by norm_num)).trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hC (by norm_num)]
  exact mul_le_mul_right (rpow_half_sum_le cells _) _

end Assembly

section Concrete

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

theorem covPolyConst_nonneg' {M : ℝ} (hM : 0 ≤ M) (p : ℕ) : 0 ≤ covPolyConst M p :=
  Finset.sum_nonneg fun l _ => div_nonneg (pow_nonneg hM l) (Nat.cast_nonneg _)

theorem card_cellBox (J H : ℕ) : (cellBox J H).card = (J + 1) * (H + 1) := by
  simp [cellBox]

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem sqrt_fNSq_respTrunc_le {k J H L : ℕ} (ρ : ℝ)
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    {ij : ℕ × ℕ} (hi : ij.1 ≤ J) (hj : ij.2 ≤ H) (v : ι) (s : ℝ) :
    Real.sqrt (factorialNormSq ρ (respTrunc k J H L U ij v s).val) ≤
      Real.sqrt (factorialNormSq ρ (U ij.1 ij.2 v s).val) := by
  have hle := boxSlot_le (k := k) (L := L) hi hj
  have hr : respTrunc k J H L U ij v s = truncateTorusHk hle (U ij.1 ij.2 v s) := by
    unfold respTrunc
    exact dite_eq_left hle
  rw [hr]
  exact sqrt_fNSq_torus_truncate_le ρ hle _

omit [Fintype ι] [DecidableEq ι] in
theorem sqrt_fNSq_retainedW_le {k J H L p D : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (Hcov : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ)
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (hord : k + 1 + D + 2 * p ≤ k + 2 * L) (v : ι) :
    Real.sqrt (factorialNormSq ρ (retainedW k J H L p D Hcov U hord v s).val) ≤
      covPolyConst (fbCovConst ρ (Hcov s) (k + 2 * L)) p *
        ∑ ij ∈ cellBox J H, Real.sqrt (factorialNormSq ρ (U ij.1 ij.2 v s).val) := by
  have hF := TorusAdj.FBound.covPolyP (E := h v) hρ (Hcov s) le_rfl p 0 (k + 2 * L)
  have hsum : Real.sqrt (factorialNormSq ρ (respSum k J H L U (cellBox J H) v s).val) ≤
      ∑ ij ∈ cellBox J H, Real.sqrt (factorialNormSq ρ (U ij.1 ij.2 v s).val) := by
    unfold respSum
    refine (sqrt_fNSq_torus_sum_le ρ _ _).trans (Finset.sum_le_sum fun ij hij => ?_)
    exact sqrt_fNSq_respTrunc_le ρ U (mem_cellBox hij).1 (mem_cellBox hij).2 v s
  unfold retainedW
  refine (sqrt_fNSq_torus_truncate_le ρ _ _).trans ?_
  refine (hF (k + 2 * L - 2 * p) (by omega) _).trans ?_
  rw [sqrt_fNSq_torusCast]
  exact mul_le_mul_of_nonneg_left hsum
    (covPolyConst_nonneg' (fbCovConst_nonneg hρ _ _) p)

omit [Fintype ι] [DecidableEq ι] in
theorem fNSq_retainedW_le {k J H L p D : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (Hcov : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ)
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (hord : k + 1 + D + 2 * p ≤ k + 2 * L) (v : ι) :
    factorialNormSq ρ (retainedW k J H L p D Hcov U hord v s).val ≤
      covPolyConst (fbCovConst ρ (Hcov s) (k + 2 * L)) p ^ 2 *
        (((cellBox J H).card : ℝ) *
          ∑ ij ∈ cellBox J H, factorialNormSq ρ (U ij.1 ij.2 v s).val) := by
  have h1 := sqrt_fNSq_retainedW_le hρ Hcov s U hord v
  have h2 := sq_sum_le_card_mul_sum_sq (s := cellBox J H)
    (f := fun ij => Real.sqrt (factorialNormSq ρ (U ij.1 ij.2 v s).val))
  calc _ = (Real.sqrt (factorialNormSq ρ (retainedW k J H L p D Hcov U hord v s).val)) ^ 2 :=
        (Real.sq_sqrt (factorialNormSq_nonneg _ _)).symm
    _ ≤ (covPolyConst (fbCovConst ρ (Hcov s) (k + 2 * L)) p *
        ∑ ij ∈ cellBox J H, Real.sqrt (factorialNormSq ρ (U ij.1 ij.2 v s).val)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    _ = covPolyConst (fbCovConst ρ (Hcov s) (k + 2 * L)) p ^ 2 *
        (∑ ij ∈ cellBox J H, Real.sqrt (factorialNormSq ρ (U ij.1 ij.2 v s).val)) ^ 2 :=
        mul_pow _ _ _
    _ ≤ covPolyConst (fbCovConst ρ (Hcov s) (k + 2 * L)) p ^ 2 *
        (((cellBox J H).card : ℝ) * ∑ ij ∈ cellBox J H,
          Real.sqrt (factorialNormSq ρ (U ij.1 ij.2 v s).val) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by
        refine congrArg _ (congrArg _ ?_)
        exact Finset.sum_congr rfl fun (ij : ℕ × ℕ) _ =>
          Real.sq_sqrt (factorialNormSq_nonneg ρ (U ij.1 ij.2 v s).val)

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem gradNormSq_respTrunc_le {k J H L D p : ℕ} (ρ : ℝ)
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v))
    {ij : ℕ × ℕ} (hi : ij.1 ≤ J) (hj : ij.2 ≤ H) (v : ι) (s : ℝ)
    (hX : k + D + 2 * p + 1 ≤ k + 2 * L)
    (hUw : truncateTorusHk (Nat.le_succ _) (Uw ij.1 ij.2 v s) = U ij.1 ij.2 v s) :
    gradNormSq (K := k + D + 2 * p) ρ (truncateTorusHk hX (respTrunc k J H L U ij v s)) ≤
      gradFactorialNormSq ρ (Uw ij.1 ij.2 v s).val := by
  have hle := boxSlot_le (k := k) (L := L) hi hj
  have hr : respTrunc k J H L U ij v s = truncateTorusHk hle (U ij.1 ij.2 v s) := by
    unfold respTrunc
    exact dite_eq_left hle
  rw [hr, ← hUw, truncateTorusHk_truncateTorusHk, truncateTorusHk_truncateTorusHk]
  exact gradNormSq_le_of_truncate (by omega) ρ _ (Uw ij.1 ij.2 v s) rfl

omit [Fintype ι] [DecidableEq ι] in
theorem gradUpTo_retainedW_le {k J H L p D : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (Hcov : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ)
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v))
    (hord : k + 1 + D + 2 * p ≤ k + 2 * L) (v : ι)
    (hUw : ∀ ij ∈ cellBox J H,
      truncateTorusHk (Nat.le_succ _) (Uw ij.1 ij.2 v s) = U ij.1 ij.2 v s) :
    gradFactorialNormSqUpTo ρ k (retainedW k J H L p D Hcov U hord v s).val ≤
      covPolyConst (fbCovConst ρ (Hcov s) (k + 2 * L)) p ^ 2 *
        (((cellBox J H).card : ℝ) *
          ∑ ij ∈ cellBox J H, gradFactorialNormSq ρ (Uw ij.1 ij.2 v s).val) := by
  have hX : k + D + 2 * p + 1 ≤ k + 2 * L := by omega
  have hZ : truncateTorusHk hX (respSum k J H L U (cellBox J H) v s) =
      ∑ ij ∈ cellBox J H, truncateTorusHk hX (respTrunc k J H L U ij v s) := by
    unfold respSum
    rw [map_sum]
  have hmain := gradUpTo_retained_le hρ (Hcov s) hord
    (retainedW k J H L p D Hcov U hord v s) (respSum k J H L U (cellBox J H) v s)
    (familyValueSum k J H L U (cellBox J H) v s)
    (fun χ hχ hp => cellInner_retainedW Hcov U hord v s hχ hp)
    (fun φ hφ => cellInner_respSum U _ (fun ij hij => mem_cellBox hij) v s hφ)
    (cellBox J H) (fun ij => truncateTorusHk hX (respTrunc k J H L U ij v s)) hZ
  refine hmain.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun ij hij => gradNormSq_respTrunc_le ρ U Uw (mem_cellBox hij).1
      (mem_cellBox hij).2 v s hX (hUw ij hij)) (Nat.cast_nonneg _)) (sq_nonneg _))

theorem scale_le_of_le {c c' n X : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c') (hn : 0 ≤ n) (hX : 0 ≤ X) :
    c ^ 2 * (n * X) ≤ (c' ^ 2 * n) * X := by
  have h1 : c ^ 2 ≤ c' ^ 2 := pow_le_pow_left₀ hc hcc 2
  calc c ^ 2 * (n * X) ≤ c' ^ 2 * (n * X) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hn hX)
    _ = (c' ^ 2 * n) * X := by ring

/-- **The strong energy of the retained field of a coarse witness.** -/
theorem retainedW_energy_le
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc) :
    AVRegularity.strongEnergyUpTo ρ B π t₀ t₁ k W ≤
      ENNReal.ofReal (covPolyConst (4 * ((k + 2 * L : ℕ) : ℝ) ^ 2) p *
        Real.sqrt ((((J + 1) * (H + 1) : ℕ)) : ℝ)) *
        ∑ ij ∈ cellBox J H, AVRegularity.strongEnergy ρ B π t₀ t₁ (U ij.1 ij.2) (Uw ij.1 ij.2) := by
  have hρ := P.rho_pos
  have hord : k + 1 + D + 2 * p ≤ k + 2 * L := by have := P.L_eq; omega
  have hκ0 : 0 ≤ covPolyConst (4 * ((k + 2 * L : ℕ) : ℝ) ^ 2) p :=
    covPolyConst_nonneg' (by positivity) p
  have hCf : ∀ s ∈ Set.Icc t₀ t₁,
      covPolyConst (fbCovConst ρ (covarianceMatrix Jm B t₀ s) (k + 2 * L)) p ≤
        covPolyConst (4 * ((k + 2 * L : ℕ) : ℝ) ^ 2) p := fun s hs =>
    gfbCovPoly_mono (fbCovConst_nonneg hρ _ _)
      (gfbCovConst_le hρ _ (k + 2 * L) (covBound_le P hs)) p
  have hCf0 : ∀ s, 0 ≤ covPolyConst (fbCovConst ρ (covarianceMatrix Jm B t₀ s) (k + 2 * L)) p :=
    fun s => covPolyConst_nonneg' (fbCovConst_nonneg hρ _ _) p
  have hWeq : ∀ t ∈ Set.Icc t₀ t₁, ∀ v, W v t =
      retainedW k J H L p D (covarianceMatrix Jm B t₀) U hord v t := fun t ht v =>
    witness_W_eq (covarianceMatrix Jm B t₀) U W hWit.1 hord ht v
  have hMem : ∀ ij ∈ cellBox J H, ∀ v,
      MemLp (Uw ij.1 ij.2 v) 2 (volume.restrict (Set.Icc t₀ t₁)) := fun ij hij v => by
    obtain ⟨f₀, -, hs, -⟩ := hR ij.1 (mem_cellBox hij).1 ij.2 (mem_cellBox hij).2
    exact hs.2.1 v
  have hTr : ∀ ij ∈ cellBox J H, ∀ v, ∀ᵐ s ∂(volume.restrict (Set.Icc t₀ t₁)),
      truncateTorusHk (Nat.le_succ _) (Uw ij.1 ij.2 v s) = U ij.1 ij.2 v s :=
    fun ij hij v => by
    obtain ⟨f₀, -, hs, -⟩ := hR ij.1 (mem_cellBox hij).1 ij.2 (mem_cellBox hij).2
    exact hs.2.2.1 v
  have hA := energy_assembly (cellBox J H) π B t₀ t₁
    (covPolyConst (4 * ((k + 2 * L : ℕ) : ℝ) ^ 2) p ^ 2 * (((J + 1) * (H + 1) : ℕ) : ℝ))
    (by positivity)
    (fun v t => factorialNormSqUpTo ρ k (W v t).val)
    (fun v s => gradFactorialNormSqUpTo ρ k (W v s).val)
    (fun ij v t => factorialNormSq ρ (U ij.1 ij.2 v t).val)
    (fun ij v s => gradFactorialNormSq ρ (Uw ij.1 ij.2 v s).val)
    (fun ij v t => factorialNormSq_nonneg _ _) (fun ij v s => gradFactorialNormSq_nonneg _ _)
    (fun ij hij v => (integrable_gradFactorialNormSq_torus (hMem ij hij v)).aemeasurable)
    (fun v t ht => by
      rw [hWeq t ht v]
      refine (factorialNormSqUpTo_le_factorialNormSq ρ k _).trans ?_
      refine (fNSq_retainedW_le hρ _ t U hord v).trans ?_
      rw [card_cellBox]
      exact scale_le_of_le (hCf0 t) (hCf t ht) (Nat.cast_nonneg _)
        (Finset.sum_nonneg fun ij _ => factorialNormSq_nonneg _ _))
    (fun v => by
      have hae := (Filter.eventually_all_finset (cellBox J H)).2 (fun ij hij => hTr ij hij v)
      filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with s hs hsI
      rw [hWeq s hsI v]
      refine (gradUpTo_retainedW_le hρ _ s U Uw hord v hs).trans ?_
      rw [card_cellBox]
      exact scale_le_of_le (hCf0 s) (hCf s hsI) (Nat.cast_nonneg _)
        (Finset.sum_nonneg fun ij _ => gradFactorialNormSq_nonneg _ _))
  have hsq : Real.sqrt (covPolyConst (4 * ((k + 2 * L : ℕ) : ℝ) ^ 2) p ^ 2 *
      (((J + 1) * (H + 1) : ℕ) : ℝ)) = covPolyConst (4 * ((k + 2 * L : ℕ) : ℝ) ^ 2) p *
        Real.sqrt ((((J + 1) * (H + 1) : ℕ)) : ℝ) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ0]
  rw [hsq] at hA
  exact hA

end Concrete

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! **The retained flux at one time.** On the window, `F_coarse(s)` is the combination of the
gradient-form adjoints of the retained diagonal part, the retained edge parts, the terminal
diagonal part and the Taylor part, applied to the truncated response sums; the terminal edge part
vanishes by acyclicity. Hence its factorial norm is bounded by the uniform constants times the
gradient energies of the responses. -/

section
section Wrap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] {K : ℕ}

/-- The pairing of a signed combination with a vanishing fourth part. -/
theorem pairing_tcombo4 {κ : Type*} [Fintype κ] (Y1 Y3 Y5 : TorusHk K E)
    (Y2 : κ → TorusHk K E) {ψ : Vec 2 → E} (hψ : Continuous ψ) {r1 r3 r5 z : ℝ} {r2 : κ → ℝ}
    (h1 : cellInner (tval Y1) ψ = r1) (h2 : ∀ u, cellInner (tval (Y2 u)) ψ = r2 u)
    (h3 : cellInner (tval Y3) ψ = r3) (h5 : cellInner (tval Y5) ψ = r5) (hz : z = 0) :
    cellInner (tval (tAdd (tAdd (tSub Y1 (tSum Y2)) Y3) Y5)) ψ =
      (r1 - ∑ u, r2 u) + (r3 - z) + r5 := by
  rw [cellInner_tAdd hψ, cellInner_tAdd hψ, cellInner_tSub hψ, cellInner_tSum hψ, h1, h3, h5,
    Finset.sum_congr rfl fun u _ => h2 u, hz, sub_zero]

/-- The factorial norm of the combination. -/
theorem sqrt_fNSq_tcombo4_le (ρ : ℝ) {κ : Type*} [Fintype κ] (Y1 Y3 Y5 : TorusHk K E)
    (Y2 : κ → TorusHk K E) :
    Real.sqrt (factorialNormSq ρ (tAdd (tAdd (tSub Y1 (tSum Y2)) Y3) Y5).val) ≤
      Real.sqrt (factorialNormSq ρ Y1.val) + ∑ u, Real.sqrt (factorialNormSq ρ (Y2 u).val) +
        Real.sqrt (factorialNormSq ρ Y3.val) + Real.sqrt (factorialNormSq ρ Y5.val) := by
  unfold tAdd tSub tSum
  have h1 := sqrt_fNSq_torus_add_le ρ (Y1 - ∑ u, Y2 u + Y3) Y5
  have h2 := sqrt_fNSq_torus_add_le ρ (Y1 - ∑ u, Y2 u) Y3
  have h3 := sqrt_fNSq_torus_add_le ρ Y1 (-∑ u, Y2 u)
  have h4 := sqrt_fNSq_torus_sum_le ρ Finset.univ Y2
  rw [sqrt_fNSq_torus_neg] at h3
  rw [sub_eq_add_neg] at h1 h2 ⊢
  linarith

end Wrap

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

omit [Fintype ι] [DecidableEq ι] in
/-- The pairing of a gradient adjoint applied to a truncated response sum. -/
theorem cellInner_gadj_resp {k J H L : ℕ}
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (S : Finset (ℕ × ℕ)) (hS : ∀ ij ∈ S, ij.1 ≤ J ∧ ij.2 ≤ H) {v u : ι} {s : ℝ}
    {T : (Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) → (Vec 2 → h u)} {m' Kc : ℕ} {ρ Cg : ℝ}
    (G : GAdj T m' Kc ρ Cg) (hK : k + (m' + 1) ≤ Kc) (hX : k + (m' + 1) ≤ k + 2 * L)
    {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : AVenhance.IsZ2Periodic ψ) (hc : Continuous (T ψ)) :
    cellInner (tval (G.adj k hK (truncateTorusHk hX (respSum k J H L U S u s)))) ψ =
      cellInner (familyValueSum k J H L U S u s) (T ψ) :=
  (G.ident k hK _ ψ hψ hp).trans (by
    rw [tval_truncateTorusHk]
    exact cellInner_respSum U S hS u s hc)

omit [Fintype ι] [DecidableEq ι] in
/-- The factorial norm of a gradient adjoint applied to a truncated response sum. -/
theorem sqrt_fNSq_gadj_resp_le {k J H L : ℕ}
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v))
    (S : Finset (ℕ × ℕ)) (hS : ∀ ij ∈ S, ij.1 ≤ J ∧ ij.2 ≤ H) {v u : ι} {s : ℝ}
    {T : (Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) → (Vec 2 → h u)} {m' Kc : ℕ} {ρ Cg : ℝ}
    (G : GAdj T m' Kc ρ Cg) (hCg : 0 ≤ Cg) (hK : k + (m' + 1) ≤ Kc)
    (hX : k + (m' + 1) ≤ k + 2 * L)
    (hUw : ∀ ij ∈ S, truncateTorusHk (Nat.le_succ _) (Uw ij.1 ij.2 u s) = U ij.1 ij.2 u s) :
    Real.sqrt (factorialNormSq ρ (G.adj k hK (truncateTorusHk hX
        (respSum k J H L U S u s))).val) ≤
      Cg * ∑ ij ∈ S, Real.sqrt (gradFactorialNormSq ρ (Uw ij.1 ij.2 u s).val) := by
  have e : G.adj k hK (truncateTorusHk hX (respSum k J H L U S u s)) =
      ∑ ij ∈ S, G.adj k hK (truncateTorusHk hX (respTrunc k J H L U ij u s)) := by
    unfold respSum
    rw [map_sum, map_sum]
  rw [e, Finset.mul_sum]
  refine (sqrt_fNSq_torus_sum_le ρ S _).trans (Finset.sum_le_sum fun ij hij => ?_)
  refine (G.gbound k hK _).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hCg)
  have hle := boxSlot_le (k := k) (L := L) (hS ij hij).1 (hS ij hij).2
  have hr : respTrunc k J H L U ij u s = truncateTorusHk hle (U ij.1 ij.2 u s) := by
    unfold respTrunc
    exact dite_eq_left hle
  rw [hr, ← hUw ij hij, truncateTorusHk_truncateTorusHk, truncateTorusHk_truncateTorusHk]
  exact gradNormSq_le_of_truncate (by omega) ρ _ (Uw ij.1 ij.2 u s) rfl

section
variable (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
include P

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem fcKc_le : k + (6 * p + D) + 1 ≤ N := (fcOrd_le P).1

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem fcOrd1 : k + (4 * p + (2 * p + D - 1) + 1) ≤ k + (6 * p + D) := by
  have := P.D_ge; omega

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem fcOrd3 : k + (2 * p + D - 1 + 1) ≤ k + (6 * p + D) := by
  have := P.D_ge; omega

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem fcOrd5 : k + (2 * p + 1) ≤ k + (6 * p + D) := by
  have := P.D_ge; omega

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem fcTr : k + (6 * p + D) ≤ k + 2 * L := by
  have := (fcOrd_le P).2; omega

/-- The retained diagonal image at one time. -/
def fcY1 (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) (v : ι) : TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)) :=
  (gT1 P (h v) (fcKc_le P) hs).adj k (fcOrd1 P) (truncateTorusHk ((fcOrd1 P).trans (fcTr P))
    (respSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) v s))

/-- The retained edge image of the source `u` at one time. -/
def fcY2 (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) (v u : ι) : TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)) :=
  (gT2 P (Nat.le_of_succ_le (fcKc_le P)) v u hs).adj k (fcOrd1 P)
    (truncateTorusHk ((fcOrd1 P).trans (fcTr P))
      (respSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s))

/-- The terminal diagonal image at one time. -/
def fcY3 (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) (v : ι) : TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)) :=
  (gT3 P (h v) (fcKc_le P) hs).adj k (fcOrd3 P) (truncateTorusHk ((fcOrd3 P).trans (fcTr P))
    (respSum k J H L U ({J} ×ˢ Finset.range (H + 1)) v s))

/-- The Taylor image at one time. -/
def fcY5 (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) (v : ι) : TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)) :=
  (gT5 P (h v) (k + (6 * p + D)) hs).adj k (fcOrd5 P)
    (truncateTorusHk ((fcOrd5 P).trans (fcTr P))
      (respSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range (H + 1)) v s))

/-- **The retained flux at one time** as the combination of the gradient adjoints. -/
theorem fc_eq_gadj {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v : ι) :
    Fc v s = tAdd (tAdd (tSub (fcY1 P U hs v) (tSum fun u => fcY2 P U hs v u))
      (fcY3 P U hs v)) (fcY5 P U hs v) := by
  have hS1 : ∀ ij ∈ Finset.range J ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hS2 : ∀ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H, ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hS3 : ∀ ij ∈ ({J} : Finset ℕ) ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hij; omega
  have hS5 : ∀ ij ∈ Finset.range (J + 1) ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  obtain ⟨Mj, hMj⟩ := jm_bound P
  refine torusHk_eq_of_cellInner fun ψ hψ hp => ?_
  have hc := hψ.continuous
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (ψ - AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
      (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p ψ)) :=
    hψ.sub (contDiff_covPolyQ_top _ p (contDiff_covPolyP_top _ p hψ))
  have hχp : AVenhance.IsZ2Periodic (ψ - AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
      (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p ψ)) := fun n x => by
    have h1 := hp n x
    have h2 := isZ2Periodic_covPolyQ (covarianceMatrix Jm B t₀ s) p
      (contDiff_covPolyP_top (covarianceMatrix Jm B t₀ s) p hψ)
      (isZ2Periodic_covPolyP (covarianceMatrix Jm B t₀ s) p hψ hp) n x
    simp only [Pi.sub_apply, h1, h2]
  have c5 : Continuous (taylorOp (covarianceMatrix Jm B t₀ s) p Jm B s ψ) :=
    ((fcT5 P hs v hMj).maps 0 le_rfl ψ (hψ.of_le (WithTop.coe_le_coe.mpr le_top)) hp).1.continuous
  have e1 := cellInner_gadj_resp (s := s) U _ hS1 (gT1 P (h v) (fcKc_le P) hs) (fcOrd1 P)
    ((fcOrd1 P).trans (fcTr P)) hψ hp (fluxAdj_regular P hs v hχ hχp).1
  have e2 := fun u => cellInner_gadj_resp (s := s) U _ hS2 (gT2 P (Nat.le_of_succ_le (fcKc_le P)) v u hs)
    (fcOrd1 P) ((fcOrd1 P).trans (fcTr P)) hψ hp (edgeAdj_regular P hs v u hχ hχp).1
  have e3 := cellInner_gadj_resp (s := s) U _ hS3 (gT3 P (h v) (fcKc_le P) hs) (fcOrd3 P)
    ((fcOrd3 P).trans (fcTr P)) hψ hp (fluxAdj_regular P hs v hψ hp).1
  have e5 := cellInner_gadj_resp (s := s) U _ hS5 (gT5 P (h v) (k + (6 * p + D)) hs) (fcOrd5 P)
    ((fcOrd5 P).trans (fcTr P)) hψ hp c5
  have hz := Finset.sum_eq_zero (s := (Finset.univ : Finset ι)) fun u _ =>
    terminal_edge_pairing_eq_zero P hR hs v u ψ
  exact (witness_Fc_component hWit hs v ψ hψ hp).trans
    (pairing_tcombo4 _ _ _ _ hc e1 e2 e3 e5 hz).symm

end
end

/-! The factorial norm of the retained flux at one time, bounded by the four uniform constants
times the gradient energies of the responses of the cells feeding each part. -/

section
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

/-- The retained diagonal constant `cqpBig · ω^{p+1} · C_D`. -/
def fcC1 (ρ a B₀ t₀ t₁ B : ℝ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (k p D : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)) : ℝ :=
  cqpBig (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) p * covRatio t₀ t₁ ρ B Jm ^ (p + 1) *
    cellCgD ρ a B₀ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal (k + (6 * p + D)) D p
      t₀ t₁ AD

/-- The retained edge constant `cqpBig · ω^{p+1} · C_E(v,u)`. -/
def fcC2 (ρ t₀ t₁ B : ℝ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (k p D H : ℕ)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v)))
    (v u : ι) : ℝ :=
  cqpBig (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) p * covRatio t₀ t₁ ρ B Jm ^ (p + 1) *
    cellCgE ρ (k + (6 * p + D)) D H p t₀ t₁ CE v u

/-- The terminal diagonal constant `C_D`. -/
def fcC3 (ρ a B₀ t₀ t₁ B : ℝ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (k p D : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)) : ℝ :=
  cellCgD ρ a B₀ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal (k + (6 * p + D)) D p
    t₀ t₁ AD

/-- The Taylor constant. -/
def fcC5 (ρ t₀ t₁ B : ℝ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (k p D : ℕ) : ℝ :=
  taylorC (k + (6 * p + D)) p (covRatio t₀ t₁ ρ B Jm) (jDev t₀ t₁ B Jm)

theorem mem_cellBox_of {J H : ℕ} {S : Finset (ℕ × ℕ)} (hS : ∀ ij ∈ S, ij.1 ≤ J ∧ ij.2 ≤ H)
    {ij : ℕ × ℕ} (hij : ij ∈ S) : ij ∈ cellBox J H := by
  have := hS ij hij
  simp only [cellBox, Finset.mem_product, Finset.mem_range]
  omega

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem cellCgE_nonneg (hρ : 0 < ρ) (Kc : ℕ) (v u : ι) : 0 ≤ cellCgE ρ Kc D H p t₀ t₁ CE v u := by
  have hg := gfbE_nonneg Kc D H p
  unfold cellCgE
  exact mul_nonneg hg (Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun d _ =>
    div_nonneg (Finset.sum_nonneg fun l _ => mul_nonneg (by positivity)
      (edgeSup_nonneg v u r d.1 l)) (by positivity))

section
variable (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
include P

/-- **The factorial norm of the retained flux at one time.** -/
theorem fc_point_le {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁)
    (hUw : ∀ ij ∈ cellBox J H, ∀ w,
      truncateTorusHk (Nat.le_succ _) (Uw ij.1 ij.2 w s) = U ij.1 ij.2 w s) (v : ι) :
    Real.sqrt (factorialNormSq ρ (Fc v s).val) ≤
      fcC1 ρ a B₀ t₀ t₁ B Jm k p D AD * ∑ ij ∈ Finset.range J ×ˢ Finset.range (H + 1),
          Real.sqrt (gradFactorialNormSq ρ (Uw ij.1 ij.2 v s).val) +
        ∑ u, fcC2 ρ t₀ t₁ B Jm k p D H CE v u *
          ∑ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H,
            Real.sqrt (gradFactorialNormSq ρ (Uw ij.1 ij.2 u s).val) +
        fcC3 ρ a B₀ t₀ t₁ B Jm k p D AD * ∑ ij ∈ ({J} : Finset ℕ) ×ˢ Finset.range (H + 1),
          Real.sqrt (gradFactorialNormSq ρ (Uw ij.1 ij.2 v s).val) +
        fcC5 ρ t₀ t₁ B Jm k p D * ∑ ij ∈ Finset.range (J + 1) ×ˢ Finset.range (H + 1),
          Real.sqrt (gradFactorialNormSq ρ (Uw ij.1 ij.2 v s).val) := by
  have hS1 : ∀ ij ∈ Finset.range J ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hS2 : ∀ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H, ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hS3 : ∀ ij ∈ ({J} : Finset ℕ) ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hij; omega
  have hS5 : ∀ ij ∈ Finset.range (J + 1) ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hρ := P.rho_pos
  have hσ : 0 ≤ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal := ENNReal.toReal_nonneg
  have hω := covRatio_nonneg t₀ t₁ ρ B Jm
  have hq : 0 ≤ cqpBig (4 * ((k + (6 * p + D) : ℕ) : ℝ) ^ 2) p *
      covRatio t₀ t₁ ρ B Jm ^ (p + 1) :=
    mul_nonneg (cqpBig_nonneg (by positivity) p) (pow_nonneg hω _)
  have hC1 : 0 ≤ fcC1 ρ a B₀ t₀ t₁ B Jm k p D AD := mul_nonneg hq (cellCgD_nonneg P hσ _)
  have hC2 : ∀ u, 0 ≤ fcC2 ρ t₀ t₁ B Jm k p D H CE v u := fun u =>
    mul_nonneg hq (cellCgE_nonneg hρ _ v u)
  have hC3 : 0 ≤ fcC3 ρ a B₀ t₀ t₁ B Jm k p D AD := cellCgD_nonneg P hσ _
  have hC5 : 0 ≤ fcC5 ρ t₀ t₁ B Jm k p D := by
    have hJ : 0 ≤ jDev t₀ t₁ B Jm := ENNReal.toReal_nonneg
    unfold fcC5 taylorC
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (pow_nonneg (mul_nonneg (by positivity) hω) p)) (by positivity)
  rw [fc_eq_gadj P hR hWit hs v]
  refine (sqrt_fNSq_tcombo4_le ρ _ _ _ _).trans
    (add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_)
  · exact (sqrt_fNSq_gadj_resp_le U Uw _ hS1 (gT1 P (h v) (fcKc_le P) hs) hC1 (fcOrd1 P)
      ((fcOrd1 P).trans (fcTr P)) (fun ij hij => hUw ij (mem_cellBox_of hS1 hij) v) : _)
  · exact Finset.sum_le_sum fun u _ => (sqrt_fNSq_gadj_resp_le U Uw _ hS2
      (gT2 P (Nat.le_of_succ_le (fcKc_le P)) v u hs) (hC2 u) (fcOrd1 P)
      ((fcOrd1 P).trans (fcTr P)) (fun ij hij => hUw ij (mem_cellBox_of hS2 hij) u) : _)
  · exact (sqrt_fNSq_gadj_resp_le U Uw _ hS3 (gT3 P (h v) (fcKc_le P) hs) hC3 (fcOrd3 P)
      ((fcOrd3 P).trans (fcTr P)) (fun ij hij => hUw ij (mem_cellBox_of hS3 hij) v) : _)
  · exact (sqrt_fNSq_gadj_resp_le U Uw _ hS5 (gT5 P (h v) (k + (6 * p + D)) hs) hC5 (fcOrd5 P)
      ((fcOrd5 P).trans (fcTr P)) (fun ij hij => hUw ij (mem_cellBox_of hS5 hij) v) : _)

end
end

end AVRegularity.CycleComparison.Coarse
end
