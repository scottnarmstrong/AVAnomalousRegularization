-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Coarse.Defect.DFBound
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.CycleComparison.Coarse.Fact.GradFluxIdent
public import AVRegularity.Statements.Intermediate.CycleComparison.IsCoarseWitness
public import AVRegularity.CycleComparison.Coarse.Exists.Cell
public import AVRegularity.CycleComparison.Coarse.Defect.DriftConjugation
public import AVRegularity.Statements.Intermediate.CycleComparison.TorusJetOrder

@[expose] public noncomputable section

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleComparison.Coarse

/-! An abstract integrand of a weak identity tested with a first-order field: a drift pairing, a
diffusion pairing and a flux pairing, each with `L²` factors. It is integrable on the cell, bounded
by a constant times the norm of the test, and subtractive in the test. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure (Vec 2)}

/-- The abstract integrand. -/
def weakIntegrand (bk : Fin 2 → Vec 2 → ℝ) (B : ℝ) (J Z : Fin 2 → Vec 2 → E) (φ0 : Vec 2 → E)
    (φ1 : Fin 2 → Vec 2 → E) (x : Vec 2) : ℝ :=
  -(∑ k : Fin 2, bk k x * inner ℝ (J k x) (φ0 x)) - B * ∑ k : Fin 2, inner ℝ (J k x) (φ1 k x)
    - ∑ k : Fin 2, inner ℝ (Z k x) (φ1 k x)

theorem weakIntegrand_integrable_and_bound {bk : Fin 2 → Vec 2 → ℝ} {Cb : ℝ}
    (hbm : ∀ k, AEStronglyMeasurable (bk k) μ) (hb : ∀ k x, |bk k x| ≤ Cb) (B : ℝ)
    {J Z : Fin 2 → Vec 2 → E} {MJ MZ : ℝ} (hJ : ∀ k, MemLp (J k) 2 μ)
    (hJb : ∀ k, (eLpNorm (J k) 2 μ).toReal ≤ MJ) (hZ : ∀ k, MemLp (Z k) 2 μ)
    (hZb : ∀ k, (eLpNorm (Z k) 2 μ).toReal ≤ MZ) {φ0 : Vec 2 → E} {φ1 : Fin 2 → Vec 2 → E}
    {Mφ : ℝ} (hφ0 : MemLp φ0 2 μ) (hφ0b : (eLpNorm φ0 2 μ).toReal ≤ Mφ)
    (hφ1 : ∀ k, MemLp (φ1 k) 2 μ) (hφ1b : ∀ k, (eLpNorm (φ1 k) 2 μ).toReal ≤ Mφ) :
    Integrable (weakIntegrand bk B J Z φ0 φ1) μ ∧
      |∫ x, weakIntegrand bk B J Z φ0 φ1 x ∂μ| ≤ (2 * Cb * MJ + 2 * |B| * MJ + 2 * MZ) * Mφ := by
  have hCb : 0 ≤ Cb := (abs_nonneg _).trans (hb 0 0)
  have hMJ : ∀ k, 0 ≤ MJ := fun k => ENNReal.toReal_nonneg.trans (hJb k)
  have hMZ : 0 ≤ MZ := ENNReal.toReal_nonneg.trans (hZb 0)
  have hMφ : 0 ≤ Mφ := ENNReal.toReal_nonneg.trans hφ0b
  -- integrability of the pieces
  have i1 : ∀ k, Integrable (fun x => bk k x * inner ℝ (J k x) (φ0 x)) μ := fun k => by
    have hm : MemLp (fun x => bk k x • J k x) 2 μ :=
      MemLp.of_le ((hJ k).const_smul Cb) ((hbm k).smul (hJ k).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => by
          simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hCb]
          exact mul_le_mul_of_nonneg_right (hb k x) (norm_nonneg _))
    exact (integrable_inner_memLp hm hφ0).congr (Filter.Eventually.of_forall fun x => by
      simp only [real_inner_smul_left])
  have i2 : ∀ k, Integrable (fun x => inner ℝ (J k x) (φ1 k x)) μ := fun k =>
    integrable_inner_memLp (hJ k) (hφ1 k)
  have i3 : ∀ k, Integrable (fun x => inner ℝ (Z k x) (φ1 k x)) μ := fun k =>
    integrable_inner_memLp (hZ k) (hφ1 k)
  have I1 := integrable_finsetSum (Finset.univ : Finset (Fin 2)) fun k _ => i1 k
  have I2 := integrable_finsetSum (Finset.univ : Finset (Fin 2)) fun k _ => i2 k
  have I3 := integrable_finsetSum (Finset.univ : Finset (Fin 2)) fun k _ => i3 k
  have hI : Integrable (weakIntegrand bk B J Z φ0 φ1) μ := (I1.neg.sub (I2.const_mul B)).sub I3
  refine ⟨hI, ?_⟩
  -- the bound
  have h1 := integral_sub (I1.neg.sub (I2.const_mul B)) I3
  have h2 := integral_sub I1.neg (I2.const_mul B)
  simp only [Pi.sub_apply, Pi.neg_apply] at h1 h2
  have e : ∫ x, weakIntegrand bk B J Z φ0 φ1 x ∂μ =
      -(∑ k : Fin 2, ∫ x, bk k x * inner ℝ (J k x) (φ0 x) ∂μ)
        - B * ∑ k : Fin 2, ∫ x, inner ℝ (J k x) (φ1 k x) ∂μ
        - ∑ k : Fin 2, ∫ x, inner ℝ (Z k x) (φ1 k x) ∂μ := by
    unfold weakIntegrand
    rw [h1, h2, integral_neg, integral_const_mul, integral_finsetSum _ fun k _ => i1 k,
      integral_finsetSum _ fun k _ => i2 k, integral_finsetSum _ fun k _ => i3 k]
  have b1 : ∀ k, |∫ x, bk k x * inner ℝ (J k x) (φ0 x) ∂μ| ≤ Cb * (MJ * Mφ) := fun k =>
    (abs_integral_mul_inner_le (hbm k) (hb k) (hJ k) hφ0).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul (hJb k) hφ0b ENNReal.toReal_nonneg (hMJ k)) hCb)
  have b2 : ∀ k, |∫ x, inner ℝ (J k x) (φ1 k x) ∂μ| ≤ MJ * Mφ := fun k =>
    (abs_integral_inner_le (hJ k) (hφ1 k)).trans
      (mul_le_mul (hJb k) (hφ1b k) ENNReal.toReal_nonneg (hMJ k))
  have b3 : ∀ k, |∫ x, inner ℝ (Z k x) (φ1 k x) ∂μ| ≤ MZ * Mφ := fun k =>
    (abs_integral_inner_le (hZ k) (hφ1 k)).trans
      (mul_le_mul (hZb k) (hφ1b k) ENNReal.toReal_nonneg hMZ)
  rw [e]
  simp only [Fin.sum_univ_two]
  obtain ⟨a0l, a0r⟩ := abs_le.1 (b1 0)
  obtain ⟨a1l, a1r⟩ := abs_le.1 (b1 1)
  obtain ⟨d0l, d0r⟩ := abs_le.1 (b3 0)
  obtain ⟨d1l, d1r⟩ := abs_le.1 (b3 1)
  have hBc : |B * (∫ x, inner ℝ (J 0 x) (φ1 0 x) ∂μ + ∫ x, inner ℝ (J 1 x) (φ1 1 x) ∂μ)| ≤
      |B| * (2 * (MJ * Mφ)) := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg B)
    exact (abs_add_le _ _).trans (by linarith [b2 0, b2 1])
  obtain ⟨hBl, hBr⟩ := abs_le.1 hBc
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg B]

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! The retained field of a coarse witness: on the window, `W(t)` is the covariance polynomial
`𝖯_p(t)` applied (in the adjoint sense) to the sum of the responses truncated to the common order
`k + 2L`. Hence `(W(t), χ) = (A_sum(t), 𝖯_p(t) χ)` for every `C^{2p}` periodic test field `χ`,
not only smooth ones. -/

section
section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Additivity of `cellInner` in its left argument over a finite sum. -/
theorem cellInner_finsetSum_left {ι : Type*} (s : Finset ι) (g : ι → Vec 2 → E)
    (ψ : Vec 2 → E)
    (h : ∀ i ∈ s, Integrable (fun x => inner ℝ (g i x) (ψ x))
      (volume.restrict AVenhance.unitCube)) :
    cellInner (fun x => ∑ i ∈ s, g i x) ψ = ∑ i ∈ s, cellInner (g i) ψ := by
  unfold cellInner
  simp_rw [sum_inner]
  exact integral_finsetSum s h

end General

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- One response truncated to the common order `k + 2L` (zero off the box). -/
def respTrunc (k J H L : ℕ) (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (ij : ℕ × ℕ) (v : ι) (t : ℝ) : TorusHk (k + 2 * L) (h v) :=
  if hle : k + 2 * L ≤ coarseSlot k J H L ij.1 ij.2 then truncateTorusHk hle (U ij.1 ij.2 v t)
  else 0

/-- The truncated sum of the responses over a set of cells. -/
def respSum (k J H L : ℕ) (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (S : Finset (ℕ × ℕ)) (v : ι) (t : ℝ) : TorusHk (k + 2 * L) (h v) :=
  ∑ ij ∈ S, respTrunc k J H L U ij v t

theorem boxSlot_le {k J H L i j : ℕ} (hi : i ≤ J) (hj : j ≤ H) :
    k + 2 * L ≤ coarseSlot k J H L i j := by
  unfold coarseSlot
  have : 2 ≤ J + H + 2 - i - j := by omega
  have := Nat.mul_le_mul_right L this
  omega

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem tval_respTrunc {k J H L : ℕ}
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)) {ij : ℕ × ℕ}
    (hi : ij.1 ≤ J) (hj : ij.2 ≤ H) (v : ι) (t : ℝ) :
    tval (respTrunc k J H L U ij v t) = tval (U ij.1 ij.2 v t) := by
  unfold respTrunc
  split_ifs with hle
  · exact tval_truncateTorusHk _ _
  · exact absurd (boxSlot_le hi hj) hle

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- **The truncated sum tests as the family value sum.** -/
theorem cellInner_respSum {k J H L : ℕ}
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (S : Finset (ℕ × ℕ)) (hS : ∀ ij ∈ S, ij.1 ≤ J ∧ ij.2 ≤ H) (v : ι) (t : ℝ)
    {φ : Vec 2 → h v} (hφ : Continuous φ) :
    cellInner (tval (respSum k J H L U S v t)) φ =
      cellInner (familyValueSum k J H L U S v t) φ := by
  unfold respSum familyValueSum
  rw [gcellInner_tval_finsetSum S _ hφ, cellInner_finsetSum_left S
    (fun ij x => (U ij.1 ij.2 v t).toFunction.jet (valueIndex2 (coarseSlot k J H L ij.1 ij.2)) x)
    φ fun ij _ => integrable_tval_inner (U ij.1 ij.2 v t) hφ]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [tval_respTrunc U (hS ij hij).1 (hS ij hij).2]
  rfl

/-- The box of cells `0 ≤ i ≤ J`, `0 ≤ j ≤ H`. -/
abbrev cellBox (J H : ℕ) : Finset (ℕ × ℕ) := Finset.range (J + 1) ×ˢ Finset.range (H + 1)

theorem mem_cellBox {J H : ℕ} {ij : ℕ × ℕ} (h : ij ∈ cellBox J H) : ij.1 ≤ J ∧ ij.2 ≤ H := by
  simp only [cellBox, Finset.mem_product, Finset.mem_range] at h
  omega

/-- The candidate retained field: `𝖯_p(t)` applied, in the adjoint sense, to the truncated sum of
the responses, at the order `k + 1 + D`. -/
def retainedW (k J H L p D : ℕ) (Hcov : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (hord : k + 1 + D + 2 * p ≤ k + 2 * L) (v : ι) (t : ℝ) : TorusHk (k + 1 + D) (h v) :=
  truncateTorusHk (by omega : k + 1 + D ≤ k + 2 * L - 2 * p)
    ((TorusAdj.covPolyP (E := h v) (Hcov t) le_rfl p 0 (k + 2 * L)).adj (k + 2 * L - 2 * p)
      (by omega) (torusCast (by omega : k + 2 * L = k + 2 * L - 2 * p + 2 * p)
        (respSum k J H L U (cellBox J H) v t)))

omit [Fintype ι] [DecidableEq ι] in
/-- The adjoint identity of the candidate retained field, for `C^{2p}` periodic tests. -/
theorem cellInner_retainedW {k J H L p D : ℕ} (Hcov : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (hord : k + 1 + D + 2 * p ≤ k + 2 * L) (v : ι) (t : ℝ) {χ : Vec 2 → h v}
    (hχ : ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) χ) (hp : AVenhance.IsZ2Periodic χ) :
    cellInner (tval (retainedW k J H L p D Hcov U hord v t)) χ =
      cellInner (familyValueSum k J H L U (cellBox J H) v t) (covPolyP (Hcov t) p χ) := by
  have hmaps := (TorusAdj.covPolyP (E := h v) (Hcov t) le_rfl p 0 (k + 2 * L)).maps 0 le_rfl χ
    (by simpa using hχ) hp
  unfold retainedW
  rw [tval_truncateTorusHk, TorusAdj.ident _ _ _ _ χ hχ hp, tval_torusCast,
    cellInner_respSum U _ (fun ij hij => mem_cellBox hij) v t
      (by simpa using hmaps.1.continuous)]

/-- **The retained field of a witness.** On the window, `W(t)` is the candidate retained field. -/
theorem witness_W_eq {k J H L p D : ℕ} {t₀ t₁ : ℝ} (Hcov : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v))
    (hW : ∀ t ∈ Set.Icc t₀ t₁, ∀ φ : ∀ v, Vec 2 → h v,
      (∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v)) → (∀ v, AVenhance.IsZ2Periodic (φ v)) →
      ∑ v, cellInner (fun x => (W v t).toFunction.jet (valueIndex2 (k + 1 + D)) x) (φ v)
        = ∑ v, cellInner (familyValueSum k J H L U (cellBox J H) v t)
            (covPolyP (Hcov t) p (φ v)))
    (hord : k + 1 + D + 2 * p ≤ k + 2 * L) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) (v : ι) :
    W v t = retainedW k J H L p D Hcov U hord v t := by
  refine torusHk_eq_of_cellInner fun φ hφ hp => ?_
  let Φ : ∀ w, Vec 2 → h w := Function.update (fun _ => 0) v φ
  have hΦs : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Φ w) := fun w => by
    by_cases hw : w = v
    · subst hw; simpa [Φ] using hφ
    · simp only [Φ, Function.update_of_ne hw]; exact contDiff_zero_fun
  have hΦp : ∀ w, AVenhance.IsZ2Periodic (Φ w) := fun w => by
    by_cases hw : w = v
    · subst hw; simpa [Φ] using hp
    · intro n x; simp [Φ, Function.update_of_ne hw]
  have hI := hW t ht Φ hΦs hΦp
  rw [Finset.sum_eq_single v (fun w _ hw => by
      simp only [Φ, Function.update_of_ne hw]; simp [cellInner])
      (fun h => absurd (Finset.mem_univ v) h),
    Finset.sum_eq_single v (fun w _ hw => by
      simp only [Φ, Function.update_of_ne hw, covPolyP_zero_field]; simp [cellInner])
      (fun h => absurd (Finset.mem_univ v) h)] at hI
  simp only [Φ, Function.update_self] at hI
  change cellInner (tval (W v t)) φ = _ at hI
  rw [hI, cellInner_retainedW Hcov U hord v t (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hp]
end

/-! Bookkeeping for family value sums: pairings are additive over disjoint unions of cells, and
the predecessor sums of the response-flux identities, summed over the box of cells, are the
family sums over the shifted boxes. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem integrable_familyValueSum_inner {k J H L : ℕ}
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (S : Finset (ℕ × ℕ)) (v : ι) (s : ℝ) {X : Vec 2 → h v} (hX : Continuous X) :
    Integrable (fun x => inner ℝ (familyValueSum k J H L U S v s x) (X x))
      (volume.restrict AVenhance.unitCube) := by
  unfold familyValueSum
  simp_rw [sum_inner]
  exact integrable_finsetSum _ fun ij _ => integrable_tval_inner (U ij.1 ij.2 v s) hX

/-- A pairing with a family sum is the sum of the pairings of its cells. -/
theorem cellInner_familyValueSum {k J H L : ℕ}
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (S : Finset (ℕ × ℕ)) (v : ι) (s : ℝ) {X : Vec 2 → h v} (hX : Continuous X) :
    cellInner (familyValueSum k J H L U S v s) X =
      ∑ ij ∈ S, cellInner (tval (U ij.1 ij.2 v s)) X := by
  unfold familyValueSum cellInner
  simp_rw [sum_inner]
  exact integral_finsetSum _ fun ij _ => integrable_tval_inner (U ij.1 ij.2 v s) hX

/-- Pairings with family sums are additive over disjoint unions of cells. -/
theorem cellInner_familyValueSum_union {k J H L : ℕ}
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    {S₁ S₂ : Finset (ℕ × ℕ)} (hd : Disjoint S₁ S₂) (v : ι) (s : ℝ) {X : Vec 2 → h v}
    (hX : Continuous X) :
    cellInner (familyValueSum k J H L U (S₁ ∪ S₂) v s) X =
      cellInner (familyValueSum k J H L U S₁ v s) X +
        cellInner (familyValueSum k J H L U S₂ v s) X := by
  have e : familyValueSum k J H L U (S₁ ∪ S₂) v s = fun x =>
      familyValueSum k J H L U S₁ v s x + familyValueSum k J H L U S₂ v s x := by
    funext x
    unfold familyValueSum
    rw [Finset.sum_union hd]
  rw [e]
  unfold cellInner
  simp_rw [inner_add_left]
  exact integral_add (integrable_familyValueSum_inner U S₁ v s hX)
    (integrable_familyValueSum_inner U S₂ v s hX)

/-- The cell box splits off its last diagonal column. -/
theorem cellBox_eq_union_diag (J H : ℕ) :
    cellBox J H = (Finset.range J ×ˢ Finset.range (H + 1)) ∪ ({J} ×ˢ Finset.range (H + 1)) := by
  ext ⟨i, j⟩
  simp only [cellBox, Finset.mem_union, Finset.mem_product, Finset.mem_range,
    Finset.mem_singleton]
  omega

theorem disjoint_diag (J H : ℕ) :
    Disjoint (Finset.range J ×ˢ Finset.range (H + 1)) ({J} ×ˢ Finset.range (H + 1)) := by
  rw [Finset.disjoint_left]
  rintro ⟨i, j⟩ h1 h2
  simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at h1 h2
  omega

/-- The cell box splits off its last edge row. -/
theorem cellBox_eq_union_edge (J H : ℕ) :
    cellBox J H = (Finset.range (J + 1) ×ˢ Finset.range H) ∪ (Finset.range (J + 1) ×ˢ {H}) := by
  ext ⟨i, j⟩
  simp only [cellBox, Finset.mem_union, Finset.mem_product, Finset.mem_range,
    Finset.mem_singleton]
  omega

theorem disjoint_edge (J H : ℕ) :
    Disjoint (Finset.range (J + 1) ×ˢ Finset.range H) (Finset.range (J + 1) ×ˢ ({H} : Finset ℕ)) := by
  rw [Finset.disjoint_left]
  rintro ⟨i, j⟩ h1 h2
  simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at h1 h2
  omega

/-- Reindexing of the diagonal predecessors. -/
theorem sum_box_pred1 (J H : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ ij ∈ cellBox J H, (if ij.1 = 0 then 0 else g (ij.1 - 1) ij.2) =
      ∑ ij ∈ Finset.range J ×ˢ Finset.range (H + 1), g ij.1 ij.2 := by
  simp only [cellBox]
  rw [Finset.sum_product, Finset.sum_product, Finset.sum_range_succ']
  simp

/-- Reindexing of the edge predecessors. -/
theorem sum_box_pred2 (J H : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ ij ∈ cellBox J H, (if ij.2 = 0 then 0 else g ij.1 (ij.2 - 1)) =
      ∑ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H, g ij.1 ij.2 := by
  simp only [cellBox]
  rw [Finset.sum_product, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range_succ']
  simp

/-- The diagonal predecessors summed over the box. -/
theorem sum_cellInner_pred1 {k J H L : ℕ}
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)) (v : ι) (s : ℝ)
    {X : Vec 2 → h v} (hX : Continuous X) :
    ∑ ij ∈ cellBox J H, cellInner ((if ij.1 = 0 then fun _ _ _ => 0
        else fun w s x => (U (ij.1 - 1) ij.2 w s).toFunction.jet
          (valueIndex2 (coarseSlot k J H L (ij.1 - 1) ij.2)) x) v s) X =
      cellInner (familyValueSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) v s) X := by
  have hterm : ∀ ij : ℕ × ℕ, cellInner ((if ij.1 = 0 then fun _ _ _ => 0
      else fun w s x => (U (ij.1 - 1) ij.2 w s).toFunction.jet
        (valueIndex2 (coarseSlot k J H L (ij.1 - 1) ij.2)) x) v s) X =
      if ij.1 = 0 then 0 else cellInner (tval (U (ij.1 - 1) ij.2 v s)) X := fun ij => by
    by_cases hi : ij.1 = 0
    · simp only [hi, ↓reduceIte]; simp [cellInner]
    · simp only [hi, ↓reduceIte]; rfl
  rw [Finset.sum_congr rfl fun ij _ => hterm ij,
    sum_box_pred1 J H (fun i j => cellInner (tval (U i j v s)) X),
    cellInner_familyValueSum U _ v s hX]

/-- The edge predecessors summed over the box. -/
theorem sum_cellInner_pred2 {k J H L : ℕ}
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)) (u : ι) (s : ℝ)
    {X : Vec 2 → h u} (hX : Continuous X) :
    ∑ ij ∈ cellBox J H, cellInner ((if ij.2 = 0 then fun _ _ _ => 0
        else fun w s x => (U ij.1 (ij.2 - 1) w s).toFunction.jet
          (valueIndex2 (coarseSlot k J H L ij.1 (ij.2 - 1))) x) u s) X =
      cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s) X := by
  have hterm : ∀ ij : ℕ × ℕ, cellInner ((if ij.2 = 0 then fun _ _ _ => 0
      else fun w s x => (U ij.1 (ij.2 - 1) w s).toFunction.jet
        (valueIndex2 (coarseSlot k J H L ij.1 (ij.2 - 1))) x) u s) X =
      if ij.2 = 0 then 0 else cellInner (tval (U ij.1 (ij.2 - 1) u s)) X := fun ij => by
    by_cases hj : ij.2 = 0
    · simp only [hj, ↓reduceIte]; simp [cellInner]
    · simp only [hj, ↓reduceIte]; rfl
  rw [Finset.sum_congr rfl fun ij _ => hterm ij,
    sum_box_pred2 J H (fun i j => cellInner (tval (U i j u s)) X),
    cellInner_familyValueSum U _ u s hX]
end

/-! The retained flux of a coarse witness one component at a time: testing the witness identity
of `F_coarse` with a test field supported in one component `v` isolates `F_coarse,v`, paired with
`F_p^*(I - 𝖰_p𝖯_p)`, the `(v,u)` blocks of `𝖯_p F_E^*(I - 𝖰_p𝖯_p)`, the terminal operators and
the Taylor operator. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The Taylor test operator `ψ ↦ (p!)⁻¹ 𝒞^p ∑_{k,l} (𝖩(s) - B I)_{kl} ∂_l ψ_k`. -/
def taylorOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (p : ℕ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B s : ℝ)
    (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) : Vec 2 → E :=
  ((p.factorial : ℝ)⁻¹) • (AVRegularity.covOperator Hc)^[p]
    (fun x => ∑ k' : Fin 2, ∑ l : Fin 2,
      (Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l) •
        fderiv ℝ (fun y => ψ y k') x (basisVec l))

/-- The `(v,u)` block of `F_E(s)^*`. -/
def edgeBlock (D H : ℕ)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v)))
    (s : ℝ) (v u : ι) (χ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) : Vec 2 → h u :=
  fun x => ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
    AVRegularity.wordAdjoint (d.1 - 1) (fun y => ContinuousLinearMap.adjoint (CE r v u d s y) (χ y)) x

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem taylorOp_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B s : ℝ) :
    taylorOp Hc p Jm B s (0 : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) = 0 := by
  unfold taylorOp
  have e : (fun x => ∑ k' : Fin 2, ∑ l : Fin 2,
      (Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l) •
        fderiv ℝ (fun y => (0 : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) y k') x (basisVec l)) =
      (0 : Vec 2 → E) := by
    funext x
    simp
  rw [e, covLin_iterate_zero, smul_zero]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- The edge flux adjoint of a family supported in one component. -/
theorem edgeFluxAdjoint_single (D H : ℕ)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v)))
    (s : ℝ) (v u : ι) (χ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) :
    AVRegularity.edgeFluxAdjoint D H CE s
        (Function.update (fun w => (0 : Vec 2 → PiLp 2 (fun _ : Fin 2 => h w))) v χ) u =
      edgeBlock D H CE s v u χ := by
  funext x
  unfold AVRegularity.edgeFluxAdjoint edgeBlock
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single v]
  · simp
  · intro w _ hw
    simp only [Function.update_of_ne hw]
    refine Finset.sum_eq_zero fun d _ => ?_
    have e : (fun y => ContinuousLinearMap.adjoint (CE r w u d s y)
        ((0 : Vec 2 → PiLp 2 (fun _ : Fin 2 => h w)) y)) = fun _ => 0 := by
      funext y; simp
    rw [e, wordAdjoint_zero_field]
  · intro h; exact absurd (Finset.mem_univ v) h

/-- **The retained flux one component at a time.** -/
theorem witness_Fc_component {t₀ t₁ B : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p k J L : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm Hcov : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm Hcov U W Fc)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v : ι) (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    cellInner (tval (Fc v s)) ψ =
      (cellInner (familyValueSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) v s)
          (AVRegularity.coarseFluxAdjoint D b AD (Hcov s) p s
            (ψ - AVRegularity.covPolyQ (Hcov s) p (AVRegularity.covPolyP (Hcov s) p ψ)))
        - ∑ u, cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s)
          (AVRegularity.covPolyP (Hcov s) p (edgeBlock D H CE s v u
            (ψ - AVRegularity.covPolyQ (Hcov s) p (AVRegularity.covPolyP (Hcov s) p ψ)))))
      + (cellInner (familyValueSum k J H L U ({J} ×ˢ Finset.range (H + 1)) v s)
          (AVRegularity.coarseFluxAdjoint D b AD (Hcov s) p s ψ)
        - ∑ u, cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ {H}) u s)
          (AVRegularity.covPolyP (Hcov s) p (edgeBlock D H CE s v u ψ)))
      + cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range (H + 1)) v s)
          (taylorOp (Hcov s) p Jm B s ψ) := by
  let Ψ : ∀ w, Vec 2 → PiLp 2 (fun _ : Fin 2 => h w) := Function.update (fun _ => 0) v ψ
  have hΨs : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Ψ w) := fun w => by
    by_cases hw : w = v
    · subst hw; simpa [Ψ] using hψ
    · simp only [Ψ, Function.update_of_ne hw]; exact contDiff_zero_fun
  have hΨp : ∀ w, AVenhance.IsZ2Periodic (Ψ w) := fun w => by
    by_cases hw : w = v
    · subst hw; simpa [Ψ] using hp
    · intro n x; simp [Ψ, Function.update_of_ne hw]
  have hI := hWit.2 s hs Ψ hΨs hΨp
  have hz : ∀ w, w ≠ v → Ψ w = 0 := fun w hw => by simp only [Ψ, Function.update_of_ne hw]
  have hQP0 : ∀ w, w ≠ v → Ψ w - AVRegularity.covPolyQ (Hcov s) p
      (AVRegularity.covPolyP (Hcov s) p (Ψ w)) = 0 := fun w hw => by
    rw [hz w hw, covPolyP_zero_field, covPolyQ_zero_field, sub_zero]
  have hfam : (fun w => Ψ w - AVRegularity.covPolyQ (Hcov s) p
      (AVRegularity.covPolyP (Hcov s) p (Ψ w))) = Function.update (fun _ => 0) v
      (ψ - AVRegularity.covPolyQ (Hcov s) p (AVRegularity.covPolyP (Hcov s) p ψ)) := by
    funext w
    by_cases hw : w = v
    · subst hw; simp [Ψ]
    · rw [hQP0 w hw, Function.update_of_ne hw]
  have hΨv : Ψ v = ψ := by simp [Ψ]
  have e1 : ∑ w, cellInner (fun x => (Fc w s).toFunction.jet (valueIndex2 k) x) (Ψ w) =
      cellInner (tval (Fc v s)) ψ := by
    rw [Finset.sum_eq_single v (fun w _ hw => by rw [hz w hw]; simp [cellInner])
      (fun h => absurd (Finset.mem_univ v) h), hΨv]
    rfl
  have e2 : ∑ w, cellInner (familyValueSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) w s)
      (AVRegularity.coarseFluxAdjoint D b AD (Hcov s) p s
        (Ψ w - AVRegularity.covPolyQ (Hcov s) p (AVRegularity.covPolyP (Hcov s) p (Ψ w)))) =
      cellInner (familyValueSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) v s)
        (AVRegularity.coarseFluxAdjoint D b AD (Hcov s) p s
          (ψ - AVRegularity.covPolyQ (Hcov s) p (AVRegularity.covPolyP (Hcov s) p ψ))) := by
    rw [Finset.sum_eq_single v (fun w _ hw => by
      rw [hQP0 w hw, coarseFluxAdjoint_zero_field]; simp [cellInner])
      (fun h => absurd (Finset.mem_univ v) h), hΨv]
  have e3 : ∑ w, cellInner (familyValueSum k J H L U ({J} ×ˢ Finset.range (H + 1)) w s)
      (AVRegularity.coarseFluxAdjoint D b AD (Hcov s) p s (Ψ w)) =
      cellInner (familyValueSum k J H L U ({J} ×ˢ Finset.range (H + 1)) v s)
        (AVRegularity.coarseFluxAdjoint D b AD (Hcov s) p s ψ) := by
    rw [Finset.sum_eq_single v (fun w _ hw => by
      rw [hz w hw, coarseFluxAdjoint_zero_field]; simp [cellInner])
      (fun h => absurd (Finset.mem_univ v) h), hΨv]
  have e5 : ∑ w, cellInner
      (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range (H + 1)) w s)
      (((p.factorial : ℝ)⁻¹) • (AVRegularity.covOperator (Hcov s))^[p]
        (fun x => ∑ k' : Fin 2, ∑ l : Fin 2,
          (Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l) •
            fderiv ℝ (fun y => Ψ w y k') x (basisVec l))) =
      cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range (H + 1)) v s)
        (taylorOp (Hcov s) p Jm B s ψ) := by
    rw [Finset.sum_eq_single v (fun w _ hw => by
      have e := taylorOp_zero (E := h w) (Hcov s) p Jm B s
      unfold taylorOp at e
      rw [hz w hw, e]; simp [cellInner])
      (fun h => absurd (Finset.mem_univ v) h), hΨv]
    rfl
  have e24 : ∀ u, AVRegularity.edgeFluxAdjoint D H CE s Ψ u = edgeBlock D H CE s v u ψ :=
    fun u => edgeFluxAdjoint_single D H CE s v u ψ
  change cellInner (tval (Fc v s)) ψ = _
  rw [← e1, hI, e2, e3, e5, hfam]
  simp only [e24, edgeFluxAdjoint_single]
end

/-! The weak identity of a response tested with a time-dependent test field
`Φ(t) = ∑ₖ cₖ(t) ψₖ`: by the product rule for indefinite integrals,
`(U(t), Φ(t)) - (U(t₀), Φ(t₀)) = ∫_{(t₀,t]} [(U(s), Φ'(s)) + r(s; Φ(s))] ds`. -/

section
section Integrand

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem integrable_respIntegrand (B : ℝ) (b : ℝ → Vec 2 → Vec 2) {K : ℕ}
    (Uw : ℝ → TorusHk (K + 1) E) (G : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => E)))
    {ψ : Vec 2 → E} (hψ : ContDiff ℝ 1 ψ) {s : ℝ} (hbs : Continuous (b s)) :
    Integrable (respIntegrand B b Uw G ψ s) (volume.restrict AVenhance.unitCube) := by
  have hJ : ∀ k : Fin 2, MemLp ((Uw s).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩) 2
      (volume.restrict AVenhance.unitCube) := fun k =>
    (Uw s).toFunction.hasPeriodicWeakJet.2.1 _
  have hGk : ∀ k : Fin 2, MemLp (fun x => (G s).toFunction.jet (valueIndex2 K) x k) 2
      (volume.restrict AVenhance.unitCube) := fun k =>
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => E) k).comp_memLp'
      ((G s).toFunction.hasPeriodicWeakJet.2.1 _)
  have hd : ∀ k : Fin 2, Continuous (fun x => fderiv ℝ ψ x (basisVec k)) := fun k =>
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hbk : ∀ k : Fin 2, Continuous (fun x => b s x k) := fun k => (continuous_apply k).comp hbs
  have h1 : Integrable (fun x => ∑ k : Fin 2, b s x k * inner ℝ ((Uw s).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ x) (ψ x))
      (volume.restrict AVenhance.unitCube) :=
    integrable_finsetSum _ fun k _ =>
      (integrable_inner_continuous (hJ k) ((hbk k).smul hψ.continuous)).congr
        (ae_of_all _ fun x => by
          change inner ℝ _ (b s x k • ψ x) = _
          rw [real_inner_smul_right])
  have h2 : Integrable (fun x => ∑ k : Fin 2, inner ℝ ((Uw s).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ x) (fderiv ℝ ψ x (basisVec k)))
      (volume.restrict AVenhance.unitCube) :=
    integrable_finsetSum _ fun k _ => integrable_inner_continuous (hJ k) (hd k)
  have h3 : Integrable (fun x => ∑ k : Fin 2, inner ℝ ((G s).toFunction.jet (valueIndex2 K) x k)
      (fderiv ℝ ψ x (basisVec k))) (volume.restrict AVenhance.unitCube) :=
    integrable_finsetSum _ fun k _ => integrable_inner_continuous (hGk k) (hd k)
  exact (h1.neg.sub (h2.const_mul B)).sub h3

/-- The integrand is linear in the test field. -/
theorem respIntegrand_lincomb (B : ℝ) (b : ℝ → Vec 2 → Vec 2) {K : ℕ}
    (Uw : ℝ → TorusHk (K + 1) E) (G : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => E)))
    {κ : Type} [Fintype κ] (c : κ → ℝ) (ψ : κ → Vec 2 → E) (hψ : ∀ m, ContDiff ℝ 1 (ψ m))
    (s : ℝ) (x : Vec 2) :
    respIntegrand B b Uw G (fun y => ∑ m, c m • ψ m y) s x =
      ∑ m, c m * respIntegrand B b Uw G (ψ m) s x := by
  have hdiff : ∀ m, DifferentiableAt ℝ (ψ m) x := fun m => (hψ m).differentiable one_ne_zero x
  have hfd : ∀ k : Fin 2, fderiv ℝ (fun y => ∑ m, c m • ψ m y) x (basisVec k) =
      ∑ m, c m • fderiv ℝ (ψ m) x (basisVec k) := by
    intro k
    have hs := fderiv_fun_sum (u := Finset.univ) (A := fun m y => c m • ψ m y) (x := x)
      (fun m _ => (hdiff m).const_smul (c m))
    rw [hs]
    simp only [FunLike.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [fderiv_fun_const_smul (hdiff m)]
    rfl
  set J : Fin 2 → E := fun k =>
    (Uw s).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ x
  set Gk : Fin 2 → E := fun k => (G s).toFunction.jet (valueIndex2 K) x k
  have hR : ∀ m, respIntegrand B b Uw G (ψ m) s x =
      -(b s x 0 * inner ℝ (J 0) (ψ m x) + b s x 1 * inner ℝ (J 1) (ψ m x))
        - B * (inner ℝ (J 0) (fderiv ℝ (ψ m) x (basisVec 0)) +
          inner ℝ (J 1) (fderiv ℝ (ψ m) x (basisVec 1)))
        - (inner ℝ (Gk 0) (fderiv ℝ (ψ m) x (basisVec 0)) +
          inner ℝ (Gk 1) (fderiv ℝ (ψ m) x (basisVec 1))) := fun m => by
    simp only [respIntegrand, Fin.sum_univ_two, J, Gk]
  have hL : respIntegrand B b Uw G (fun y => ∑ m, c m • ψ m y) s x =
      -(b s x 0 * ∑ m, c m * inner ℝ (J 0) (ψ m x) + b s x 1 * ∑ m, c m * inner ℝ (J 1) (ψ m x))
        - B * (∑ m, c m * inner ℝ (J 0) (fderiv ℝ (ψ m) x (basisVec 0)) +
          ∑ m, c m * inner ℝ (J 1) (fderiv ℝ (ψ m) x (basisVec 1)))
        - (∑ m, c m * inner ℝ (Gk 0) (fderiv ℝ (ψ m) x (basisVec 0)) +
          ∑ m, c m * inner ℝ (Gk 1) (fderiv ℝ (ψ m) x (basisVec 1))) := by
    simp only [respIntegrand, Fin.sum_univ_two, hfd, inner_sum, real_inner_smul_right, J, Gk]
  rw [hL]
  simp only [hR, mul_sub, mul_neg, mul_add, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, Finset.mul_sum]
  have e1 : ∀ m, c m * (b s x 0 * inner ℝ (J 0) (ψ m x)) =
      b s x 0 * (c m * inner ℝ (J 0) (ψ m x)) := fun m => by ring
  have e2 : ∀ m, c m * (b s x 1 * inner ℝ (J 1) (ψ m x)) =
      b s x 1 * (c m * inner ℝ (J 1) (ψ m x)) := fun m => by ring
  have e3 : ∀ m, c m * (B * inner ℝ (J 0) (fderiv ℝ (ψ m) x (basisVec 0))) =
      B * (c m * inner ℝ (J 0) (fderiv ℝ (ψ m) x (basisVec 0))) := fun m => by ring
  have e4 : ∀ m, c m * (B * inner ℝ (J 1) (fderiv ℝ (ψ m) x (basisVec 1))) =
      B * (c m * inner ℝ (J 1) (fderiv ℝ (ψ m) x (basisVec 1))) := fun m => by ring
  simp only [e1, e2, e3, e4, ← Finset.mul_sum]

end Integrand

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **The weak identity of a response with a time-dependent test field.** -/
theorem resp_timeTest {B t₀ t₁ : ℝ} {b : ℝ → Vec 2 → Vec 2} {K : ℕ}
    {f₀ : ∀ v, TorusHk K (h v)} {G : ∀ v, ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => h v))}
    {U : ∀ v, ℝ → TorusHk K (h v)} {Uw : ∀ v, ℝ → TorusHk (K + 1) (h v)}
    (hsol : IsCoupledWeakSolutionTorus B t₀ t₁ b 2 (fun _ => K) (fun _ _ _ _ _ => 0) f₀ G
      (fun _ _ => 0) U Uw)
    (hbc : ∀ s ∈ Set.Icc t₀ t₁, Continuous (b s)) (v : ι) (Φ : TimeTest (h v) t₀ t₁)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    IntegrableOn (fun s => cellInner (tval (U v s)) (Φ.deriv s) +
        respRhs B b (Uw v) (G v) (Φ.val s) s) (Set.Ioc t₀ t) ∧
      cellInner (tval (U v t)) (Φ.val t) - cellInner (tval (U v t₀)) (Φ.val t₀) =
        ∫ s in Set.Ioc t₀ t, (cellInner (tval (U v s)) (Φ.deriv s) +
          respRhs B b (Uw v) (G v) (Φ.val s) s) := by
  have hsub : Set.Icc t₀ t ⊆ Set.Icc t₀ t₁ := Set.Icc_subset_Icc le_rfl ht.2
  have hIoc : Set.Ioc t₀ t ⊆ Set.Ioc t₀ t₁ := Set.Ioc_subset_Ioc le_rfl ht.2
  have hψ1 : ∀ k, ContDiff ℝ 1 (Φ.ψ k) := fun k => (Φ.smooth k).of_le (by exact_mod_cast le_top)
  have h0 : U v t₀ = f₀ v := hsol.2.2.2.1 v
  -- the per-field identities
  have hg : ∀ k, ∀ s ∈ Set.Icc t₀ t, cellInner (tval (U v s)) (Φ.ψ k) =
      cellInner (tval (U v t₀)) (Φ.ψ k) + ∫ σ in Set.Ioc t₀ s, respRhs B b (Uw v) (G v) (Φ.ψ k) σ :=
    fun k s hs => by
      have := (resp_weak_smooth hsol v (hsub hs) (hψ1 k) (Φ.per k)).2
      rw [h0]; linarith
  have hgi : ∀ k, IntegrableOn (fun σ => respRhs B b (Uw v) (G v) (Φ.ψ k) σ) (Set.Ioc t₀ t) :=
    fun k => (resp_weak_smooth hsol v ht (hψ1 k) (Φ.per k)).1
  have hc : ∀ k, ∀ s ∈ Set.Icc t₀ t, Φ.c k s = Φ.c k t₀ + ∫ σ in Set.Ioc t₀ s, Φ.dc k σ :=
    fun k s hs => Φ.prim k s (hsub hs)
  have hpr := fun k => product_rule_integral ht.1 ((Φ.dc_int k).mono_set hIoc) (hgi k) (hc k)
    (hg k)
  -- linearity in the test field
  have hcont : ∀ k, Continuous (Φ.ψ k) := fun k => (Φ.smooth k).continuous
  have hlin_val : ∀ s, cellInner (tval (U v s)) (Φ.val s) =
      ∑ k, Φ.c k s * cellInner (tval (U v s)) (Φ.ψ k) := fun s => by
    unfold TimeTest.val
    rw [gcellInner_finsetSum_right _ _ (fun k x => Φ.c k s • Φ.ψ k x) fun k _ =>
      integrable_tval_inner (U v s) ((hcont k).const_smul _)]
    exact Finset.sum_congr rfl fun k _ => cellInner_smul_right _ _ _
  have hlin_der : ∀ s, cellInner (tval (U v s)) (Φ.deriv s) =
      ∑ k, Φ.dc k s * cellInner (tval (U v s)) (Φ.ψ k) := fun s => by
    unfold TimeTest.deriv
    rw [gcellInner_finsetSum_right _ _ (fun k x => Φ.dc k s • Φ.ψ k x) fun k _ =>
      integrable_tval_inner (U v s) ((hcont k).const_smul _)]
    exact Finset.sum_congr rfl fun k _ => cellInner_smul_right _ _ _
  have hlin_rhs : ∀ s ∈ Set.Ioc t₀ t, respRhs B b (Uw v) (G v) (Φ.val s) s =
      ∑ k, Φ.c k s * respRhs B b (Uw v) (G v) (Φ.ψ k) s := fun s hs => by
    have hbs := hbc s (hsub (Set.Ioc_subset_Icc_self hs))
    unfold respRhs TimeTest.val
    rw [integral_congr_ae (ae_of_all _ fun x =>
      respIntegrand_lincomb B b (Uw v) (G v) (fun k => Φ.c k s) Φ.ψ hψ1 s x),
      integral_finsetSum _ fun k _ =>
        (integrable_respIntegrand B b (Uw v) (G v) (hψ1 k) hbs).const_mul _]
    exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  have hpt : ∀ s ∈ Set.Ioc t₀ t, cellInner (tval (U v s)) (Φ.deriv s) +
      respRhs B b (Uw v) (G v) (Φ.val s) s =
      ∑ k, (Φ.dc k s * cellInner (tval (U v s)) (Φ.ψ k) +
        Φ.c k s * respRhs B b (Uw v) (G v) (Φ.ψ k) s) := fun s hs => by
    rw [hlin_der, hlin_rhs s hs, ← Finset.sum_add_distrib]
  have hint : IntegrableOn (fun s => ∑ k, (Φ.dc k s * cellInner (tval (U v s)) (Φ.ψ k) +
      Φ.c k s * respRhs B b (Uw v) (G v) (Φ.ψ k) s)) (Set.Ioc t₀ t) :=
    integrable_finsetSum _ fun k _ => (hpr k).1
  refine ⟨hint.congr_fun (fun s hs => (hpt s hs).symm) measurableSet_Ioc, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_finsetSum _ fun k _ => (hpr k).1,
    hlin_val, hlin_val, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => (hpr k).2
end

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! Formal adjoints of the test operators of the retained flux `F_coarse` of a coarse witness:
`F_p^*`, `I - 𝖰_p 𝖯_p`, their composite, the `(v,u)` blocks of `𝖯_p F_E^*` (alone and composed
with `I - 𝖰_p 𝖯_p`), and the Taylor operator `ψ ↦ (p!)⁻¹ 𝒞^p ∑_{k,l} (𝖩 - B I)_{kl} ∂_l ψ_k`. -/

section Single

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- `F_p(s)^*`, of order `2p + D`. -/
def TorusAdj.fluxAdj (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (b : ℝ → Vec 2 → Vec 2) (D p : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (R Kc Q : ℕ) (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hAp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l) :
    TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) =>
      AVRegularity.coarseFluxAdjoint D b AD Hc p s ψ) (2 * p + D) R Kc
      (fluxConstF M (commConst M Kc Bb) (diagConst D Kc BA) p) :=
  (((TorusAdj.sumMem (Finset.Icc 1 p) fun l hl =>
        (TorusAdj.sumMem (Finset.range l) fun a ha =>
          TorusAdj.coarseCommTerm (E := E) Hc hM b s R Kc Q p D l a (Finset.mem_range.mp ha)
            (Finset.mem_Icc.mp hl).2 hQR hQK hb hbp Bb hBb).smul ((l.factorial : ℝ)⁻¹)).mono
      le_rfl le_rfl (le_of_eq (by
        unfold fluxConstA
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]))).sub
    (((TorusAdj.covPolyP (E := E) Hc hM p R Kc).comp
      (TorusAdj.diagFlux (E := E) D AD s (R + 2 * p) Kc Q (by omega) (by omega) hA hAp BA hBA)
      le_rfl le_rfl).liftOrder (by omega : 2 * p + (D - 1) ≤ 2 * p + D))).ofOp
    (by
      funext ψ x
      simp [AVRegularity.coarseFluxAdjoint, Finset.sum_apply])

/-- `I - 𝖰_p 𝖯_p`, of order `4p`. -/
def TorusAdj.idSubQP (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (p R Kc : ℕ) :
    TorusAdj (fun ψ : Vec 2 → E => ψ - AVRegularity.covPolyQ Hc p (AVRegularity.covPolyP Hc p ψ))
      (4 * p) R Kc (1 + covPolyConst M p * covPolyConst M p) :=
  (((TorusAdj.id (E := E) R Kc).liftOrder (Nat.zero_le (4 * p))).sub
    (((TorusAdj.covPolyQ (E := E) Hc hM p R Kc).comp
      (TorusAdj.covPolyP (E := E) Hc hM p (R + 2 * p) Kc) le_rfl le_rfl).ofOrder
      (by omega : 2 * p + 2 * p = 4 * p))).ofOp (by funext ψ; rfl)

/-- The Taylor operator `ψ ↦ (p!)⁻¹ 𝒞^p ∑_{k,l} c_{kl} ∂_l ψ_k`, of order `2p + 1`. -/
def TorusAdj.taylor (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (c : Matrix (Fin 2) (Fin 2) ℝ) (p R Kc : ℕ) :
    TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) =>
      ((p.factorial : ℝ)⁻¹) • (AVRegularity.covOperator Hc)^[p]
        (fun x => ∑ k : Fin 2, ∑ l : Fin 2, c k l • fderiv ℝ (fun y => ψ y k) x (basisVec l)))
      (2 * p + 1) R Kc
      (|((p.factorial : ℝ)⁻¹)| * (M ^ p * ∑ k : Fin 2, ∑ l : Fin 2,
        |c k l| * (1 * ((Kc.factorial : ℝ) * 1)))) :=
  (((TorusAdj.covIter (E := E) Hc hM p R Kc).comp
    (TorusAdj.sum (Finset.univ : Finset (Fin 2)) fun k =>
      TorusAdj.sum (Finset.univ : Finset (Fin 2)) fun l =>
        (((TorusAdj.coordDeriv (E := E) l (R + 2 * p) Kc).comp
          (TorusAdj.componentOp (E := E) k (R + 2 * p + 1) Kc) le_rfl le_rfl).ofOrder
          (by omega : 1 + 0 = 1)).smul (c k l)) le_rfl le_rfl).smul
    ((p.factorial : ℝ)⁻¹)).ofOp (by funext ψ; rfl)

end Single

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! The response side of the conjugation identity at one time: the right side of the weak
identity of a response, tested with a smooth periodic field `χ`, is
`(U, b·∇χ) + B (U, Δχ) - (G, ∇χ)`, once the gradient-level field of the response agrees with the
response at that time. -/

section
/-- The Laplacian `∑_k ∂_k ∂_k χ`. -/
def lapField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (χ : Vec 2 → E) :
    Vec 2 → E :=
  fun x => ∑ k : Fin 2, fderiv ℝ (fun y => fderiv ℝ χ y (basisVec k)) x (basisVec k)

section Single

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The first jets of a gradient-level field are those of its truncation. -/
theorem jet_one_of_truncate {K : ℕ} (hK : 1 ≤ K) {X : TorusHk (K + 1) E} {Y : TorusHk K E}
    (htr : truncateTorusHk (Nat.le_succ K) X = Y) (k : Fin 2) :
    X.toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ =
      torusJetOrder Y 1 (fun _ => k) := by
  rw [torusJetOrder_of_le Y hK, ← htr]
  rfl

/-- **The response integrand at one time.** -/
theorem respRhs_eq_pairings {B : ℝ} {b : ℝ → Vec 2 → Vec 2} {K : ℕ} (hK : 1 ≤ K)
    {Uw : ℝ → TorusHk (K + 1) E} {U : ℝ → TorusHk K E}
    (G : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => E))) {s : ℝ}
    (htr : truncateTorusHk (Nat.le_succ K) (Uw s) = U s)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (b s)) (hbp : AVenhance.IsZ2Periodic (b s))
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (b s) x (basisVec k) k = 0)
    {χ : Vec 2 → E} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hp : AVenhance.IsZ2Periodic χ) :
    respRhs B b Uw G χ s =
      cellInner (tval (U s)) (driftDeriv (b s) χ) + B * cellInner (tval (U s)) (lapField χ)
        - cellInner (fun x => (G s).toFunction.jet (valueIndex2 K) x) (gradField χ) := by
  have hJ := fun k => jet_one_of_truncate hK htr k
  have hb1 : ContDiff ℝ 1 (b s) := hb.of_le (by exact_mod_cast le_top)
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by exact_mod_cast le_top)
  have hχ2 : ContDiff ℝ 2 χ := by simpa using contDiff_top_nat hχ 2
  obtain ⟨i1, e1⟩ := integral_drift_jet (U s) hK hb1 hbp hdiv hχ1 hp
  obtain ⟨i2, e2⟩ := integral_diffusion_jet (U s) hK hχ2 hp
  have hGk : ∀ k : Fin 2, MemLp (fun x => (G s).toFunction.jet (valueIndex2 K) x k) 2
      (volume.restrict AVenhance.unitCube) := fun k =>
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => E) k).comp_memLp'
      ((G s).toFunction.hasPeriodicWeakJet.2.1 _)
  have hd : ∀ k : Fin 2, Continuous (fun x => fderiv ℝ χ x (basisVec k)) := fun k =>
    (hχ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have i3 : Integrable (fun x => ∑ k : Fin 2, inner ℝ ((G s).toFunction.jet (valueIndex2 K) x k)
      (fderiv ℝ χ x (basisVec k))) (volume.restrict AVenhance.unitCube) :=
    integrable_finsetSum _ fun k _ => integrable_inner_continuous (hGk k) (hd k)
  have e3 : ∫ x in AVenhance.unitCube, ∑ k : Fin 2,
      inner ℝ ((G s).toFunction.jet (valueIndex2 K) x k) (fderiv ℝ χ x (basisVec k)) =
      cellInner (fun x => (G s).toFunction.jet (valueIndex2 K) x) (gradField χ) := by
    unfold cellInner
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [PiLp.inner_apply, gradField_apply, partialOp_apply]
  have hint : ∀ x, respIntegrand B b Uw G χ s x =
      -(∑ k : Fin 2, b s x k * inner ℝ (torusJetOrder (U s) 1 (fun _ => k) x) (χ x))
        - B * ∑ k : Fin 2, inner ℝ (torusJetOrder (U s) 1 (fun _ => k) x)
          (fderiv ℝ χ x (basisVec k))
        - ∑ k : Fin 2, inner ℝ ((G s).toFunction.jet (valueIndex2 K) x k)
          (fderiv ℝ χ x (basisVec k)) := fun x => by
    simp only [respIntegrand, hJ]
  unfold respRhs
  have h1 := integral_sub (i1.neg.sub (i2.const_mul B)) i3
  have h2 := integral_sub i1.neg (i2.const_mul B)
  simp only [Pi.sub_apply, Pi.neg_apply] at h1 h2
  rw [integral_congr_ae (ae_of_all _ hint), h1, h2, integral_neg, integral_const_mul, e1, e2, e3]
  have e4 : driftDeriv (b s) χ = fun x => ∑ k : Fin 2, b s x k • fderiv ℝ χ x (basisVec k) := rfl
  rw [e4]
  unfold lapField
  ring

end Single
end

/-! The formal adjoint of the `(v,u)` block `χ ↦ 𝖯_p (F_E^* χ)_u` of the retained flux, built from
the edge coefficients extended by zero outside `1 ≤ r ≤ H`. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- `χ ↦ 𝖯_p (F_E(s)^* χ)_u` for a test `χ` in component `v`: order `2p + D - 1`. -/
def TorusAdj.edgeAdj (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (D H p : ℕ)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v)))
    (v u : ι) (s : ℝ) (R Kc Q : ℕ) (hQR : R + 2 * p + D ≤ Q) (hQK : Kc ≤ Q)
    (hC : ∀ r ∈ Finset.Icc 1 H, ∀ d, ContDiff ℝ (Q : ℕ) (CE r v u d s))
    (hCp : ∀ r ∈ Finset.Icc 1 H, ∀ d, AVenhance.IsZ2Periodic (CE r v u d s))
    (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (edgeExt H CE r v u d s) l x‖ ≤ BE r d.1 l) :
    TorusAdj (fun χ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP Hc p (edgeBlock D H CE s v u χ)) (2 * p + (D - 1)) R Kc
      (covPolyConst M p * edgeConst D H Kc BE) :=
  ((TorusAdj.covPolyP (E := h u) Hc hM p R Kc).comp
    (TorusAdj.edgeFluxBlock (X := h v) (Y := h u) D H (fun r d => edgeExt H CE r v u d s)
      (R + 2 * p) Kc Q (by omega) hQK
      (fun r d => by
        by_cases hr : r ∈ Finset.Icc 1 H
        · rw [edgeExt_of_mem hr]; exact hC r hr d
        · have he : edgeExt (D := D) H CE r v u d s = 0 := by simp [edgeExt, hr]
          rw [he]; exact contDiff_const)
      (fun r d => by
        by_cases hr : r ∈ Finset.Icc 1 H
        · rw [edgeExt_of_mem hr]; exact hCp r hr d
        · have he : edgeExt (D := D) H CE r v u d s = 0 := by simp [edgeExt, hr]
          rw [he]; intro n x; rfl)
      BE hBE) le_rfl le_rfl).ofOp (by
    funext χ
    congr 1
    funext x
    unfold edgeBlock
    refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun d _ => ?_
    simp only [edgeExt_of_mem hr])
end

/-! The retained flux of a coarse witness is, on the window, the combination of formal adjoints of
its five test operators applied to the truncated response sums; hence its norm is bounded by the
operator constants times the norms of these sums. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

theorem cellInner_tval_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ} (X Y : TorusHk K E)
    {ψ : Vec 2 → E} (hψ : Continuous ψ) :
    cellInner (tval (X - Y)) ψ = cellInner (tval X) ψ - cellInner (tval Y) ψ := by
  rw [sub_eq_add_neg, cellInner_tval_add _ _ hψ, cellInner_tval_neg, ← sub_eq_add_neg]

/-- The pairing of a signed combination of periodic Sobolev fields. -/
theorem cellInner_tval_combo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ} {κ : Type*} [Fintype κ]
    (X1 X3 X5 : TorusHk K E) (X2 X4 : κ → TorusHk K E) {ψ : Vec 2 → E} (hψ : Continuous ψ) :
    cellInner (tval (X1 - ∑ u, X2 u + X3 - ∑ u, X4 u + X5)) ψ =
      (cellInner (tval X1) ψ - ∑ u, cellInner (tval (X2 u)) ψ)
        + (cellInner (tval X3) ψ - ∑ u, cellInner (tval (X4 u)) ψ) + cellInner (tval X5) ψ := by
  rw [cellInner_tval_add _ _ hψ, cellInner_tval_sub _ _ hψ, cellInner_tval_add _ _ hψ,
    cellInner_tval_sub _ _ hψ, gcellInner_tval_finsetSum _ _ hψ, gcellInner_tval_finsetSum _ _ hψ]
  ring

/-- The pairing of a signed combination, from the pairings of its parts. -/
theorem pairing_combo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ} {κ : Type*} [Fintype κ]
    (Y1 Y3 Y5 : TorusHk K E) (Y2 Y4 : κ → TorusHk K E) {ψ : Vec 2 → E} (hψ : Continuous ψ)
    {r1 r3 r5 : ℝ} {r2 r4 : κ → ℝ} (h1 : cellInner (tval Y1) ψ = r1)
    (h2 : ∀ u, cellInner (tval (Y2 u)) ψ = r2 u) (h3 : cellInner (tval Y3) ψ = r3)
    (h4 : ∀ u, cellInner (tval (Y4 u)) ψ = r4 u) (h5 : cellInner (tval Y5) ψ = r5) :
    cellInner (tval (Y1 - ∑ u, Y2 u + Y3 - ∑ u, Y4 u + Y5)) ψ =
      (r1 - ∑ u, r2 u) + (r3 - ∑ u, r4 u) + r5 := by
  rw [cellInner_tval_combo _ _ _ _ _ hψ, h1, h3, h5, Finset.sum_congr rfl fun u _ => h2 u,
    Finset.sum_congr rfl fun u _ => h4 u]

omit [Fintype ι] [DecidableEq ι] in
/-- The adjoint pairing of a truncated response sum. -/
theorem cellInner_adj_respSum {k J H L m R Kc : ℕ}
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (S : Finset (ℕ × ℕ)) (hS : ∀ ij ∈ S, ij.1 ≤ J ∧ ij.2 ≤ H) {v u : ι} {s : ℝ} {C : ℝ}
    {T : (Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) → (Vec 2 → h u)}
    (A : TorusAdj T m R Kc C) (hKc : k + m ≤ Kc) (hm : k + m ≤ k + 2 * L)
    {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : AVenhance.IsZ2Periodic ψ) :
    cellInner (tval (A.adj k hKc (truncateTorusHk hm (respSum k J H L U S u s)))) ψ =
      cellInner (familyValueSum k J H L U S u s) (T ψ) := by
  have hψm : ContDiff ℝ (m : WithTop ℕ∞) ψ := hψ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hψm' : ContDiff ℝ ((0 + m : ℕ) : WithTop ℕ∞) ψ := by rw [Nat.zero_add]; exact hψm
  have hcont : Continuous (T ψ) := (A.maps 0 (Nat.zero_le _) ψ hψm' hp).1.continuous
  set X : TorusHk (k + m) (h u) := truncateTorusHk hm (respSum k J H L U S u s) with hX
  have h1 : cellInner (tval (A.adj k hKc X)) ψ = cellInner (tval X) (T ψ) :=
    A.ident k hKc X ψ hψm hp
  have h2 : tval X = tval (respSum k J H L U S u s) := tval_truncateTorusHk hm _
  rw [h1, h2]
  exact cellInner_respSum U S hS u s hcont

/-- **The retained flux as a combination of adjoints.** -/
theorem witness_Fc_eq_of_adj {t₀ t₁ B : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p k J L : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm Hcov : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm Hcov U W Fc)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v : ι) {m R Kc : ℕ} (hKc : k + m ≤ Kc)
    (hm : k + m ≤ k + 2 * L) {C1 C3 C5 : ℝ} {C2 C4 : ι → ℝ}
    (T1 : TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.coarseFluxAdjoint D b AD (Hcov s) p s
        (ψ - AVRegularity.covPolyQ (Hcov s) p (AVRegularity.covPolyP (Hcov s) p ψ))) m R Kc C1)
    (T2 : ∀ u, TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP (Hcov s) p (edgeBlock D H CE s v u
        (ψ - AVRegularity.covPolyQ (Hcov s) p (AVRegularity.covPolyP (Hcov s) p ψ))))
      m R Kc (C2 u))
    (T3 : TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.coarseFluxAdjoint D b AD (Hcov s) p s ψ) m R Kc C3)
    (T4 : ∀ u, TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP (Hcov s) p (edgeBlock D H CE s v u ψ)) m R Kc (C4 u))
    (T5 : TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      taylorOp (Hcov s) p Jm B s ψ) m R Kc C5) :
    Fc v s =
      T1.adj k hKc (truncateTorusHk hm
          (respSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) v s))
        - ∑ u, (T2 u).adj k hKc (truncateTorusHk hm
          (respSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s))
        + T3.adj k hKc (truncateTorusHk hm
          (respSum k J H L U ({J} ×ˢ Finset.range (H + 1)) v s))
        - ∑ u, (T4 u).adj k hKc (truncateTorusHk hm
          (respSum k J H L U (Finset.range (J + 1) ×ˢ {H}) u s))
        + T5.adj k hKc (truncateTorusHk hm
          (respSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range (H + 1)) v s)) := by
  have hS1 : ∀ ij ∈ Finset.range J ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hS2 : ∀ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H, ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hS3 : ∀ ij ∈ ({J} : Finset ℕ) ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hij; omega
  have hS4 : ∀ ij ∈ Finset.range (J + 1) ×ˢ ({H} : Finset ℕ), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hij; omega
  have hS5 : ∀ ij ∈ Finset.range (J + 1) ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  refine torusHk_eq_of_cellInner fun ψ hψ hp => ?_
  exact (witness_Fc_component hWit hs v ψ hψ hp).trans (pairing_combo _ _ _ _ _ hψ.continuous
    (cellInner_adj_respSum U _ hS1 T1 hKc hm hψ hp)
    (fun u => cellInner_adj_respSum U _ hS2 (T2 u) hKc hm hψ hp)
    (cellInner_adj_respSum U _ hS3 T3 hKc hm hψ hp)
    (fun u => cellInner_adj_respSum U _ hS4 (T4 u) hKc hm hψ hp)
    (cellInner_adj_respSum U _ hS5 T5 hKc hm hψ hp)).symm
end

end AVRegularity.CycleComparison.Coarse
end
