-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovTruncCovGradient
public import AVRegularity.CycleComparison.ActualMeans.Transfer
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovMeanJetPoly
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
import AVRegularity.EntryTerminal.Ingredients.Frontier.InnerWrappers
import AVRegularity.EntryTerminal.Ingredients.SeedStruct.SeedStruct
public import AVRegularity.EntryTerminal.Assembly.Seed.PricedSchur
import AVRegularity.Construction.StageKernelPrice.Successor
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity
open AVRegularity.CycleComparison.Lift AVRegularity.CycleComparison.LiftMeanEntrywise
namespace AVRegularity.Construction.Residual.Presentation

/-! The explicit mean letters present the actual cell flux at finite input regularity.
Zero tested order is removed before the index shift from lift degree m to flux order d=m+1.
This is the literal identity needed by the physical coefficient producer of the cell-mean operator. -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- The explicit mean letters give the exact flux mean, rather than just its divergence. -/
theorem covTruncMeanLetter_cell_flux (sX sZ : ℕ) (hsX : max 2 D ≤ sX)
    (hsZ : max 2 D ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ ((D + N : ℕ) : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) (j : Fin 2) (v : ι) :
    fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) hh n t X z j) v =
      ∑ d ∈ Finset.Icc 2 n, ∑ α : DerivativeWord2 (d - 1), ∑ u,
        meanLetter Q Cc hh n d α t X j v u (orderedDerivative α f X u) := by
  let c := actualMeanFluxCoefficient Q Cc hh n
  have hC : fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) hh n t X z j) =
      liftApply (n - 1) (c j) (fun _ => f) t X 0 := by
    have he := covTruncCellMean_finite P sX sZ hsX hsZ Cc hseq P₀ hreserve
      hh n hhh hn hnR f hf t ht X j
    by_cases hh0 : hh = 0
    · subst hh
      simpa only [c, actualMeanFluxCoefficient, ite_true] using he
    · simpa only [c, actualMeanFluxCoefficient, ite_eq_right hh0] using he
  rw [hC]
  let F : (m : ℕ) → DerivativeWord2 m → ∀ i, h i := fun m α i =>
    ∑ u, c j m α t X 0 i u (orderedDerivative α f X u)
  have hz : (∑ α : DerivativeWord2 0, F 0 α) = 0 := by
    ext i
    have hc : ∀ α u, c j 0 α t X 0 i u = 0 := fun α u =>
      setting_actual_meanFlux_coefficient_zero_order P sX sZ
        ((by omega : 1 ≤ max 2 D).trans hsZ) Cc hseq P₀ hreserve hh hhh n hn hnR
        j t ht α X 0 i u
    simp only [F, Finset.sum_apply, hc, zero_apply, Finset.sum_const_zero, Pi.zero_apply]
  have hs := sum_range_zero_order_shift n (by omega) (fun m => ∑ α : DerivativeWord2 m, F m α) hz
  have hn' : n - 1 + 1 = n := by omega
  have he : liftApply (n - 1) (c j) (fun _ => f) t X 0 v =
      ∑ d ∈ Finset.Icc 2 n, ∑ α : DerivativeWord2 (d - 1), F (d - 1) α v := by
    simpa only [liftApply, hn', Finset.sum_apply, F] using congrFun hs v
  rw [he]
  refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun u _ => ?_
  have heq : meanLetter Q Cc hh n d α t X j v u = c j (d - 1) α t X 0 v u := by
    by_cases hh0 : hh = 0
    · subst hh
      simp only [meanLetter_zero, diagonalMeanLetter, c, actualMeanFluxCoefficient, ite_true,
        truncatedMeanCoefficient_eq n d (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2]
    · simp only [meanLetter_of_ne_zero Q Cc hh0, positiveMeanLetter, c,
        actualMeanFluxCoefficient, ite_eq_right hh0,
        truncatedMeanCoefficient_eq n d (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2]
  rw [heq]

include P in
/-- The actual dimensional pulse flux equals the explicit mean-letter flux at finite
regularity. The tested word contributes rho^(d-1), and the flux contributes one more rho. -/
theorem covTruncMeanLetter_pulse_flux (sX sZ : ℕ) (hsX : max 2 D ≤ sX)
    (hsZ : max 2 D ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 2 ≤ n) (hnR : n ≤ N + D)
    (c εc : ℝ) (hc : c ≠ 0) (chart label : ℝ → Vec 2 → Vec 2)
    (hchart : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (chart t))
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (hf : ContDiff ℝ ((D + N : ℕ) : ℕ∞) (f t))
    (ht : c⁻¹ * t ∈ Set.Icc a b) (x : Vec 2) (j : Fin 2) (v : ι) :
    pulseMeanFluxEuler c ρ εc n hh Q Cc chart label f t x v j =
      -(c⁻¹ * εc ^ n) • ∑ l : Fin 2, jacMatrix (chart t) (label t x) j l •
        ∑ d ∈ Finset.Icc 2 n, ρ ^ d • ∑ α : DerivativeWord2 (d - 1), ∑ u,
          meanLetter Q Cc hh n d α (c⁻¹ * t) (ρ⁻¹ • label t x) l v u
            (orderedDerivative α (fun y => f t (chart t y)) (label t x) u) := by
  have hct : c * (c⁻¹ * t) = t := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  let g : Vec 2 → ∀ i, h i := fun y => f t (chart t y)
  have hg : ContDiff ℝ ((D + N : ℕ) : ℕ∞) g := hf.comp ((hchart t).of_le (by exact_mod_cast (le_top : (D + N : ℕ∞) ≤ ⊤)))
  have hscaled : ContDiff ℝ ((D + N : ℕ) : ℕ∞) (fun Y => g (ρ • Y)) :=
    hg.comp (contDiff_const_smul ρ)
  have he : ∀ l : Fin 2,
      fieldCellMean (fun z => liftFluxX Q Cc
        (fun s Y => f (c * s) (chart (c * s) (ρ • Y))) hh n (c⁻¹ * t)
        (ρ⁻¹ • label t x) z l) v =
      ∑ d ∈ Finset.Icc 2 n, ρ ^ (d - 1) • ∑ α : DerivativeWord2 (d - 1), ∑ u,
        meanLetter Q Cc hh n d α (c⁻¹ * t) (ρ⁻¹ • label t x) l v u
          (orderedDerivative α g (label t x) u) := by
    intro l
    have he := covTruncMeanLetter_cell_flux P sX sZ hsX hsZ Cc hseq P₀ hreserve
      hh n hhh hn hnR (fun Y => g (ρ • Y)) hscaled (c⁻¹ * t) ht
      (ρ⁻¹ • label t x) l v
    change fieldCellMean (fun z => liftFluxX Q Cc _ hh n (c⁻¹ * t) _ z l) v = _
    have htime : liftFluxX Q Cc
        (fun s Y => f (c * s) (chart (c * s) (ρ • Y))) hh n (c⁻¹ * t) =
        liftFluxX Q Cc (fun _ Y => g (ρ • Y)) hh n (c⁻¹ * t) := by
      unfold AVRegularity.liftFluxX AVRegularity.liftApply
      simp only [hct, g]
    rw [htime, he]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hm : d - 1 ≤ D + N := by have := (Finset.mem_Icc.mp hd).2; omega
    have hword := fun α : DerivativeWord2 (d - 1) =>
      orderedDerivative_comp_smul α g (hg.of_le (by exact_mod_cast hm)) ρ (ρ⁻¹ • label t x)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hword α, smul_smul, mul_inv_cancel₀ P.ρ_pos.ne', one_smul, Pi.smul_apply, map_smul]
  unfold pulseMeanFluxEuler
  rw [Finset.sum_congr rfl fun l _ => congrArg (fun z => jacMatrix (chart t) (label t x) j l •
    (-(c⁻¹ * εc ^ n * ρ) • z)) (he l), Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_comm (-(c⁻¹ * εc ^ n))]
  congr 1
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := (by have := (Finset.mem_Icc.mp hd).1; omega)
  rw [smul_smul, smul_smul]
  congr 1
  rw [neg_mul, mul_assoc, ← pow_succ', Nat.sub_add_cancel hd1, neg_mul]

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The explicit edge coefficient formula of the glued means holds for finite smoothness and every
grade, including grade zero. Its actual flux is determined by the finite Taylor jet at the point. -/
theorem covTruncMeanLetter_ce_action_finite (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ)
    (c ρ εc : ℝ) (R : ℕ) (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ)
    (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h) (hh : ℕ) (t : ℝ)
    (hchart : ∀ k ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (chart k t))
    (hinv : ∀ k ∈ kset, ∀ y, chart k t (label k t y) = y)
    (hsupp : ∀ k ∈ kset, ϖ k t ≠ 0 → c⁻¹ * t ∈ Set.Icc (s₀ k) (s₁ k))
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (R : ℕ∞) f) (x : Vec 2) (v : ι) (j : Fin 2) :
    (∑ u : ι, ∑ d : Finset.Icc 2 R,
      AVRegularity.CycleComparison.ActualMeans.ceLetter kset ϖ c ρ εc R chart label s₀ s₁ Lb hh v u d t x
        (WithLp.toLp 2 fun α => orderedDerivative α (fun y => f y u) x) j) =
      -∑ k ∈ kset, ϖ k t • ∑ n ∈ Finset.Icc 2 R, (c⁻¹ * εc ^ n) • ∑ l : Fin 2,
        jacMatrix (chart k t) (label k t x) j l • ∑ d ∈ Finset.Icc 2 n, ρ ^ d •
          ∑ α : DerivativeWord2 (d - 1), ∑ u,
            Lb k hh n d α (c⁻¹ * t) (ρ⁻¹ • label k t x) l v u
              (orderedDerivative α (fun y => f (chart k t y)) (label k t x) u) := by
  classical
  obtain ⟨g, hg, hj⟩ :=
    AVRegularity.Construction.Preservation.Residual.FluxCancellation.smoothJetRealization R f hf x
  have hjet : ∀ u (r : ℕ) (α : DerivativeWord2 r), r ≤ R →
      orderedDerivative α (fun y => f y u) x = orderedDerivative α (fun y => g y u) x := by
    intro u r α hr
    rw [← AVRegularity.ChartTransport.orderedDerivative_apply α
      (hf.of_le (by exact_mod_cast hr)) u x,
      ← AVRegularity.ChartTransport.orderedDerivative_apply α
        (hg.of_le (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤))) u x]
    exact (congrFun (hj r α hr) u).symm
  have hcomp : ∀ k ∈ kset,
      AVRegularity.Construction.Preservation.Residual.FluxCancellation.SameJetAt R (label k t x)
        (fun y => g (chart k t y)) (fun y => f (chart k t y)) := by
    intro k hk
    apply AVRegularity.Construction.Preservation.Residual.FluxCancellation.sameJet_comp
      (label k t x) R (chart k t) g f
      ((hchart k hk).of_le (by exact_mod_cast (le_top : (R : ℕ∞) ≤ ⊤)))
      (hg.of_le (by exact_mod_cast (le_top : (R : ℕ∞) ≤ ⊤))) hf
    rw [hinv k hk x]
    exact hj
  have he := AVRegularity.CycleComparison.ActualMeans.classicalGradeFlux_edge kset ϖ c ρ εc R
    chart label s₀ s₁ (fun k _ n => Lb k hh n) (fun _ _ _ => 0) (fun _ => 0)
    (r := 1) (by decide) (fun _ => g) t hg hchart hinv hsupp x v j
  change (∑ u : ι, ∑ d : Finset.Icc 2 R,
      AVRegularity.CycleComparison.ActualMeans.ceLetter kset ϖ c ρ εc R chart label s₀ s₁ Lb hh v u d t x
        (WithLp.toLp 2 fun α => orderedDerivative α (fun y => g y u) x) j) = _ at he
  calc
    _ = ∑ u : ι, ∑ d : Finset.Icc 2 R,
        AVRegularity.CycleComparison.ActualMeans.ceLetter kset ϖ c ρ εc R chart label s₀ s₁ Lb hh v u d t x
          (WithLp.toLp 2 fun α => orderedDerivative α (fun y => g y u) x) j := by
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun d _ => ?_
      have ha : (WithLp.toLp 2 fun α : DerivativeWord2 (d.val - 1) =>
          orderedDerivative α (fun y => f y u) x) =
          WithLp.toLp 2 fun α : DerivativeWord2 (d.val - 1) =>
            orderedDerivative α (fun y => g y u) x := by
        apply PiLp.ext
        intro α
        exact hjet u (d.val - 1) α (by have := (Finset.mem_Icc.mp d.2).2; omega)
      rw [ha]
    _ = _ := he
    _ = _ := by
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      congr 1
      refine Finset.sum_congr rfl fun n hn => ?_
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun d hd => ?_
      congr 1
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun u _ => ?_
      rw [(hcomp k hk) (d - 1) α (by
        have := (Finset.mem_Icc.mp hd).2
        have := (Finset.mem_Icc.mp hn).2
        omega)]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
/-- Diagonal means above the diagonal lift cutoff vanish, including their literal flux.
The sequence cutoff is global in time, as in `IsLiftSequence`. -/
theorem covTruncMeanLetter_diagonal_cutoff (sX sZ : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (n : ℕ) (hn : N + 1 < n) (hn2 : n ≠ 2) :
    diagonalMeanFluxCoefficient Q Cc n = fun _ _ _ _ _ _ _ _ => 0 := by
  have hz : ∀ m α t X z v u, Cc 0 (n - 1) m α t X z v u = 0 :=
    hseq.2.2.1 0 (Nat.zero_le H) (n - 1) (by omega)
  funext j m α t X z v u
  simp only [diagonalMeanFluxCoefficient, weightedLiftCoefficientMean, hz,
    smul_zero, fieldCellMean, integral_zero, ite_eq_right hn2, add_zero]

include P in
/-- Above the grade-zero degree cutoff, the literal mean flux vanishes already for a
finite-regularity input. This is used to shorten the full degree range of the glued means to the
menu's range. -/
theorem covTruncMeanLetter_pulse_cutoff (sX sZ : ℕ) (hsX : max 2 D ≤ sX)
    (hsZ : max 2 D ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (P₀ : ℕ) (hreserve : P₀ + (N + D) ≤ qs)
    (n : ℕ) (hn : N + 1 < n) (hn2 : 2 ≤ n) (hnR : n ≤ N + D) (hN : 1 ≤ N)
    (c εc : ℝ) (hc : c ≠ 0) (chart label : ℝ → Vec 2 → Vec 2)
    (hchart : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (chart t))
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (hf : ContDiff ℝ ((D + N : ℕ) : ℕ∞) (f t))
    (ht : c⁻¹ * t ∈ Set.Icc a b) (x : Vec 2) (j : Fin 2) (v : ι) :
    pulseMeanFluxEuler c ρ εc n 0 Q Cc chart label f t x v j = 0 := by
  have hz := covTruncMeanLetter_diagonal_cutoff sX sZ Cc hseq n hn (by omega)
  rw [covTruncMeanLetter_pulse_flux P sX sZ hsX hsZ Cc hseq P₀ hreserve 0 n
    (Nat.zero_le _) hn2 hnR c εc hc chart label hchart f t hf ht x j v]
  have hL : meanLetter Q Cc 0 n = 0 := by
    rw [meanLetter_zero, diagonalMeanLetter, hz]
    funext d α s Y l v u
    simp only [truncatedMeanCoefficient, Pi.zero_apply, ite_self]
  simp only [hL, Pi.zero_apply, zero_apply, Finset.sum_const_zero, smul_zero]

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleComparison.Coarse
open scoped ENNReal
namespace AVRegularity.Construction.Residual.Presentation

/-! Physical scalar-jet coefficients become the exact gradient-carrier coefficient data.
The single fixed word reading pays one fewer derivative than the scalar jet.
Entrywise seminorms are normalized before applying the weighted Schur test; constants
depend on the orders, not the component family or datum. These lemmas are used by the
uniform producer from the actual letters, not as extra premises of the statement.
Degenerate cases: orders zero and one have no positive letters; one component is scalar;
empty component families and zero data use the same formulas. -/

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {K R : ℕ} {a b ρ : ℝ}
  (A : ∀ v u : ι, (d : Finset.Icc 2 R) → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h u) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h v))

/-- The actual physical scalar coefficient after reading its positive tested jet from the
gradient. The last two unused reserve levels are zero. -/
def covTruncScalarLetterCoefficient (v u : ι) (r : Fin (R + 1)) (t : ℝ) (x : Vec 2) :
    PiLp 2 (fun _ : DerivativeWord2 r.val => PiLp 2 (fun _ : Fin 2 => h u)) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h v) :=
  open Classical in
  if hr : r.val + 2 ≤ R then
    (A v u ⟨r.val + 2, Finset.mem_Icc.mpr ⟨by omega, hr⟩⟩ t x).comp
      (covTruncGradientWordCLM r.val) else 0

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] in
private theorem scalarLetter_regular
    (hs : ∀ v u d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A v u d t))
    (hp : ∀ v u d, ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (A v u d t))
    (hm : ∀ v u d, Measurable fun p : Set.Icc a b × Vec 2 => A v u d p.1 p.2)
    (hf : ∀ v u d, coefficientSeminorm ρ K a b (A v u d) ≠ ⊤) (v u : ι) (r : Fin (R + 1)) :
    (∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (covTruncScalarLetterCoefficient A v u r t)) ∧
    (∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (covTruncScalarLetterCoefficient A v u r t)) ∧
    Measurable (fun p : Set.Icc a b × Vec 2 => covTruncScalarLetterCoefficient A v u r p.1 p.2) ∧
    coefficientSeminorm ρ K a b (covTruncScalarLetterCoefficient A v u r) ≠ ⊤ := by
  classical
  by_cases hr : r.val + 2 ≤ R
  · let d : Finset.Icc 2 R := ⟨r.val + 2, Finset.mem_Icc.mpr ⟨by omega, hr⟩⟩
    have he : covTruncScalarLetterCoefficient A v u r =
        fun t x => (A v u d t x).comp (covTruncGradientWordCLM r.val) := by
      funext t x
      simp only [covTruncScalarLetterCoefficient, dite_eq_left hr, d]
    rw [he]
    refine ⟨fun t ht => (covTruncGradientWord_coefficient_regular r.val K _ (hs v u d t ht)
      (hp v u d t ht)).1,
      fun t ht => (covTruncGradientWord_coefficient_regular r.val K _ (hs v u d t ht)
        (hp v u d t ht)).2, ?_, ?_⟩
    · let Φ := (ContinuousLinearMap.compL ℝ
        (PiLp 2 (fun _ : DerivativeWord2 r.val => PiLp 2 (fun _ : Fin 2 => h u)))
        (PiLp 2 (fun _ : DerivativeWord2 (r.val + 1) => h u))
        (PiLp 2 (fun _ : Fin 2 => h v))).flip (covTruncGradientWordCLM (E := h u) r.val)
      exact Φ.continuous.measurable.comp (hm v u d)
    · exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hf v u d))
        (covTruncGradientWord_seminorm_le r.val K ρ a b (A v u d) (hs v u d))
  · have he : covTruncScalarLetterCoefficient A v u r = fun _ _ => 0 := by
      funext t x
      simp only [covTruncScalarLetterCoefficient, dite_eq_right hr]
    rw [he]
    exact ⟨fun _ _ => contDiff_const, fun _ _ _ _ => rfl, measurable_const,
      by rw [coefficientSeminorm_const_zero]; exact ENNReal.zero_ne_top⟩

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] in
private theorem scalarLetter_cost (hρ : 0 < ρ)
    (hs : ∀ v u d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A v u d t))
    (hf : ∀ v u d, coefficientSeminorm ρ K a b (A v u d) ≠ ⊤) (v u : ι) :
    (∑ r : Fin (R + 1), (coefficientSeminorm ρ K a b (covTruncScalarLetterCoefficient A v u r)).toReal *
      derivativeReserveFactor ρ K r.val) ≤ covTruncGradientCoefficientConst K R *
        ∑ d : Finset.Icc 2 R, (coefficientSeminorm ρ K a b (A v u d)).toReal / ρ ^ (d.val - 2) := by
  classical
  have hb : ∀ r : Fin (R + 1),
      (coefficientSeminorm ρ K a b (covTruncScalarLetterCoefficient A v u r)).toReal *
        derivativeReserveFactor ρ K r.val ≤
      if hr : r.val + 2 ≤ R then covTruncGradientCoefficientConst K R *
        ((coefficientSeminorm ρ K a b (A v u
          ⟨r.val + 2, Finset.mem_Icc.mpr ⟨by omega, hr⟩⟩)).toReal / ρ ^ r.val) else 0 := by
    intro r
    by_cases hr : r.val + 2 ≤ R
    · simp only [dite_eq_left hr]
      have he : covTruncScalarLetterCoefficient A v u r =
          fun t x => (A v u ⟨r.val + 2, Finset.mem_Icc.mpr ⟨by omega, hr⟩⟩ t x).comp
            (covTruncGradientWordCLM r.val) := by
        funext t x
        simp only [covTruncScalarLetterCoefficient, dite_eq_left hr]
      rw [he]
      exact covTruncGradientWord_cost r.val K R (Nat.le_of_lt_succ r.isLt) ρ a b hρ _
        (hs v u _) (hf v u _)
    · have he : covTruncScalarLetterCoefficient A v u r = fun _ _ => 0 := by
        funext t x
        simp only [covTruncScalarLetterCoefficient, dite_eq_right hr]
      simp only [he, coefficientSeminorm_const_zero, ENNReal.toReal_zero, zero_mul,
        dite_eq_right hr, le_refl]
  refine (Finset.sum_le_sum fun r _ => hb r).trans_eq ?_
  rw [Finset.mul_sum]
  exact covTruncPositiveOrder_sum R (fun d : Finset.Icc 2 R =>
    covTruncGradientCoefficientConst K R *
      ((coefficientSeminorm ρ K a b (A v u d)).toReal / ρ ^ (d.val - 2)))

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
private theorem scalarLetter_action (f : Vec 2 → ∀ i, h i)
    (hf : ∀ i, ContDiff ℝ ((K + R + 1 : ℕ) : ℕ∞) (fun x => f x i))
    (v u : ι) (t : ℝ) (x : Vec 2) :
    (∑ r : Fin (R + 1), covTruncScalarLetterCoefficient A v u r t x
      (WithLp.toLp 2 fun α : DerivativeWord2 r.val => orderedDerivative α
        (fun y => toFluxL (gradE (fun z => f z u) y)) x)) =
      ∑ d : Finset.Icc 2 R, A v u d t x
        (WithLp.toLp 2 fun α => orderedDerivative α (fun y => f y u) x) := by
  classical
  have he : ∀ r : Fin (R + 1), covTruncScalarLetterCoefficient A v u r t x
      (WithLp.toLp 2 fun α : DerivativeWord2 r.val => orderedDerivative α
        (fun y => toFluxL (gradE (fun z => f z u) y)) x) =
      if hr : r.val + 2 ≤ R then A v u ⟨r.val + 2, Finset.mem_Icc.mpr ⟨by omega, hr⟩⟩ t x
        (WithLp.toLp 2 fun α => orderedDerivative α (fun y => f y u) x) else 0 := by
    intro r
    by_cases hr : r.val + 2 ≤ R
    · simp only [covTruncScalarLetterCoefficient, dite_eq_left hr, ContinuousLinearMap.comp_apply]
      have hinput : (fun y => toFluxL (gradE (fun z => f z u) y)) =
          AVRegularity.CycleComparison.Coarse.gradField (fun y => f y u) := rfl
      rw [hinput, covTruncGradientWordCLM_jet r.val (fun y => f y u)
        ((hf u).of_le (by exact_mod_cast (by omega : r.val + 1 ≤ K + R + 1))) x]
      rfl
    · simp only [covTruncScalarLetterCoefficient, dite_eq_right hr, zero_apply]
  rw [Finset.sum_congr rfl fun r _ => he r]
  exact covTruncPositiveOrder_sum R (fun d : Finset.Icc 2 R => A v u d t x
    (WithLp.toLp 2 fun α => orderedDerivative α (fun y => f y u) x))

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] in
/-- Scalar-jet coefficients with their actual normalized entrywise budgets supply the entire
physical gradient-carrier coefficient data. No hypothesis concerns the PDE solution's energy. -/
theorem covTruncCoefficientData_of_scalar_letters (hρ : 0 < ρ) (π : ι → ℝ) (Bprice : ℝ)
    (price : ι → ι → ℝ) (hprice : ∀ v u, 0 ≤ price v u)
    (hs : ∀ v u d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A v u d t))
    (hp : ∀ v u d, ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (A v u d t))
    (hm : ∀ v u d, Measurable fun p : Set.Icc a b × Vec 2 => A v u d p.1 p.2)
    (hfin : ∀ v u d, coefficientSeminorm ρ K a b (A v u d) ≠ ⊤)
    (hcost : ∀ v u, (∑ d : Finset.Icc 2 R,
      (coefficientSeminorm ρ K a b (A v u d)).toReal / ρ ^ (d.val - 2)) ≤ price v u)
    (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * price v u ≤ Bprice)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * price v u ≤ Bprice)
    (f : ℝ → Vec 2 → ∀ i, h i)
    (hf : ∀ i, ∀ t ∈ Set.Icc a b, ContDiff ℝ ((K + R + 1 : ℕ) : ℕ∞) (fun x => f t x i))
    (hfper : ∀ i, ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (fun x => f t x i))
    (target : ∀ i, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h i))
    (ha : ∀ v, ∀ t ∈ Set.Icc a b, ∀ x, target v t x =
      ∑ u, ∑ d : Finset.Icc 2 R, A v u d t x
        (WithLp.toLp 2 fun α => orderedDerivative α (fun y => f t y u) x)) :
    Nonempty (CovTruncCoefficientData (h := h) K R a b ρ
      (covTruncGradientCoefficientConst K R * Bprice) π
      (fun v t y => toFluxL (gradE (fun z => f t z v) y)) target) := by
  have hC : 0 ≤ covTruncGradientCoefficientConst K R := by
    unfold covTruncGradientCoefficientConst
    positivity
  have hreg := scalarLetter_regular A hs hp hm hfin
  refine ⟨{
    coeff := covTruncScalarLetterCoefficient A
    smooth := fun v u r => (hreg v u r).1
    periodic := fun v u r => (hreg v u r).2.1
    measurable := fun v u r => (hreg v u r).2.2.1
    finite := fun v u r => (hreg v u r).2.2.2
    price := fun v u => covTruncGradientCoefficientConst K R * price v u
    price_nonneg := fun v u => mul_nonneg hC (hprice v u)
    coefficient_cost := fun v u => (scalarLetter_cost A hρ hs hfin v u).trans
      (mul_le_mul_of_nonneg_left (hcost v u) hC)
    row := fun v => ?_
    col := fun u => ?_
    input_smooth := fun v t ht => ?_
    input_periodic := fun v t ht z x => ?_
    action := fun v t ht x => ?_ }⟩
  · calc
      _ = covTruncGradientCoefficientConst K R * ∑ u, Real.sqrt (π u / π v) * price v u := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrow v) hC
  · calc
      _ = covTruncGradientCoefficientConst K R * ∑ v, Real.sqrt (π u / π v) * price v u := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcol u) hC
  · exact_mod_cast contDiff_gradField_nat (hf v t ht)
  · apply PiLp.ext
    intro j
    have he := fderiv_isZ2Periodic ((hf v t ht).differentiable (by simp)) (hfper v t ht) z x
    exact congrArg (fun T => T (basisVec j)) he
  · rw [ha v t ht x]
    exact Finset.sum_congr rfl fun u _ => (scalarLetter_action A (f t) (fun i => hf i t ht) v u t x).symm

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
namespace AVRegularity.Construction.Residual.Presentation

/-! Diagonal and mean bounds from uniform physical coefficient data. The generic
measurable multiplier, finite-jet realization and weighted Schur machinery are discharged.
Only the physical coefficient producer remains in each branch. The input order equals the
output order plus the mean derivative reserve. The covariance factor is separately
discharged by covTruncCovGradient using the adjoint calculus.

Degenerate cases: empty components, zero datum, dW=0, one component, and a point window are
handled by the same coefficient/operator assembly. No window-length price is introduced. -/

/-- Derivative reserve of the physical mean flux, after applying the covariance polynomial. -/
def covTruncPhysicalReserve {X : TermConstruction} (A : TermArgs X) : ℕ :=
  A.NT + A.Dt

section Context
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- The actual physical coefficients acting on the higher gradient, with uniform price C B.
The input is the actual gradient of P_pZ; the separately proved covariance operator supplies
that gradient from Z. The diagonal coefficient includes the reference-flux subtraction. -/
def CovTruncPhysicalCoefficientsAt (diagonal : Bool) (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  Nonempty (CovTruncCoefficientData (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root)
    (kc + 4 * A.pT) (covTruncPhysicalReserve A) c.tp (c.a + A.T₀)
    (c.D.termRho cr M) (C * c.D.κ (M - 1)) (c.Gw.mass c.lawW)
    (covTruncCovGradientInput c x)
    (covTruncMeanTarget c diagonal x))

/-- The physical radius and masses are positive under the existing context premises. -/
theorem covTruncPhysical_geometry (x : TermResAux c) (hΛ : 128 ≤ A.Λ) :
    0 < c.D.termRho cr M ∧ ∀ v, 0 < c.Gw.mass c.lawW v := by
  have hΛD : 128 ≤ c.D.Λ := c.data.2.2.1 ▸ hΛ
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos (by omega) X.hζ
    c.data.2.2.2.2.2.1 (Nat.sub_le M 1)
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (by omega : 1 ≤ c.D.Λ)
  have hcr : 0 < cr := lt_of_lt_of_eq one_pos x.one.symm
  have hρ : 0 < c.D.termRho cr M := mul_pos hcr (Real.sqrt_pos.mpr (mul_pos hν hh))
  have hq : 1 < c.D.q := c.data.2.1 ▸ X.hq.1
  exact ⟨hρ, fun v => Construction.Preservation.Buffer.birth_compMass_pos hq hΛD c.lawW v.1⟩
end Context

/-- The uniform physical coefficient producer for the positive-grade branch. -/
def CovTruncMeanPhysicalCoefficientsStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => CovTruncPhysicalCoefficientsAt c false x kc C

/-- Physical coefficients give the exact operator, with all generic analysis discharged. -/
theorem covTruncMeanOperator_of_physical (diagonal : Bool)
    (hPhys : TermResPrefix fun c x kc _ C _ _ => CovTruncPhysicalCoefficientsAt c diagonal x kc C) :
    TermResPrefix fun c x kc _ C _ _ => CovTruncMeanOperatorAt c diagonal x kc C := by
  have hj := termFluxPrefix_and
    (P₁ := fun c x kc C => CovTruncPhysicalCoefficientsAt c diagonal x kc C)
    (P₂ := fun c x kc C => CovTruncCovGradientAt c x kc C) hPhys covTruncCovGradient
  refine termFluxPrefix_map (P := fun c x kc C =>
    CovTruncPhysicalCoefficientsAt c diagonal x kc C ∧ CovTruncCovGradientAt c x kc C)
    (R := fun c x kc C => CovTruncMeanOperatorAt c diagonal x kc C) ?_ hj
  intro X A kc C₁ hΛ hC₁
  refine ⟨C₁ ^ 2, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hP C' hC'
  obtain ⟨⟨P⟩, ⟨Tcov⟩⟩ := hP
  obtain ⟨hρ, hπ⟩ := covTruncPhysical_geometry c x hΛ
  have hν : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos (by omega) X.hζ
    c.data.2.2.2.2.2.1 (Nat.sub_le M 1)
  have hR : kc + 4 * A.pT + covTruncPhysicalReserve A = covTruncCovGradientOrder A kc := by
    dsimp [covTruncPhysicalReserve, covTruncCovGradientOrder]
    omega
  let T := P.toFluxOperator hρ hπ
  have T' : CovTruncFluxOperator (h := fun v : CompIn c.Gw.comps => ScalarH v.1.root)
      (covTruncCovGradientOrder A kc) (kc + 4 * A.pT) (Set.Icc c.tp (c.a + A.T₀))
      (c.D.termRho cr M) (c.Gw.mass c.lawW) (C₁ * c.D.κ (M - 1))
      (covTruncCovGradientInput c x) (covTruncMeanTarget c diagonal x) := hR ▸ T
  let U := Tcov.comp T'
  have hc : (C₁ * c.D.κ (M - 1)) * C₁ = C₁ ^ 2 * c.D.κ (M - 1) := by ring
  rw [hc] at U
  refine ⟨{ U with weighted_bound := fun t ht W => ?_ }⟩
  refine (U.weighted_bound t ht W).trans ?_
  have hCb : 0 ≤ C₁ ^ 2 * c.D.κ (M - 1) := mul_nonneg (sq_nonneg _) hν.le
  have hprod := mul_le_mul_of_nonneg_right hC' hν.le
  have hcost := pow_le_pow_left₀ hCb hprod 2
  apply mul_le_mul_of_nonneg_right hcost
  exact Finset.sum_nonneg fun v _ => mul_nonneg (inv_nonneg.2 (hπ v).le)
    (factorialNormSq_nonneg _ _)

/-- Exact positive mean flux from its uniform physical coefficients. -/
theorem covTruncMean_of_physical (hPhys : CovTruncMeanPhysicalCoefficientsStatement) :
    CovTruncMeanStatement := covTruncMean_of_operator (covTruncMeanOperator_of_physical false hPhys)

end AVRegularity.Construction.Residual.Presentation
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! **The coefficient regularity of all identities of the terminal successor
(`FilterRegStatement`).**

Every component of `Gt'` has grade at most one, so its reserve is in `[0, 2]`
(`termReserve_nonneg` with `x.reserve1`). The measurability, smoothness, periodicity and finite
seminorm of every `physCoeff` of `Gt'` then come from the native lemmas applied to `Gt'` itself
with the certificate `x.cert`. The radius satisfies `ρ ≤ ε_{M-1} ≤ ε_{M-2}` for `M` large.

Degenerate case: an empty window (`CoeffReg` is a statement about all identities, not the
window). -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **`FilterRegAt` from the certificate** at a late level. -/
theorem filterRegAt
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (kc : ℕ) {CH Υ : ℝ} (hV : A.Valid) (hΛ : 128 ≤ A.Λ)
    (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ) (hcar : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀)
    (hX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT)
    (hj : j₀ + 1 ≤ M) (hM2 : 2 ≤ M) (hρε : c.D.termRho cr M ≤ c.D.eps (M - 1)) :
    FilterRegAt c kc := by
  have hb : 0 < A.bw := hV.2.2.1.1
  have hST := termCtx_slotTransverse c x hV hΛ hCH hΥ hcar hX hZ
  have hSH := termCtx_shiftInvariant c hΛ
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := by rw [hΛD]; omega
  have hlevW : c.Gw.level = M := c.weak.2.2.1
  have hbirth : ∀ w : CompIn c.Gw.comps, w.1.births = [] := c.weak.2.2.2.2.1
  have hlev : c.Gt'.level = M - 1 := by rw [c.succ.2.1, hlevW]
  have hres : ∀ w : CompIn c.Gt'.comps, 0 ≤ compReserve kW w.1 := fun w =>
    termReserve_nonneg x.reserve1
      (termGrade_le_one (fun u => by simp [compGrade, hbirth u]) c.succ w)
  have hres2 : ∀ w : CompIn c.Gt'.comps, compReserve kW w.1 ≤ 2 := fun w =>
    (AVRegularity.Providers.CascadeInvariants.compReserve_le_one kW w.1).trans (by norm_num)
  have hnat := c.succ.2.2.2.1
  have hεpos : 0 < c.D.eps (M - 1 - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hν : 0 < c.D.κ (M - 1) :=
    CycleReference.bandChain_pos (by omega : 1 ≤ A.Λ) X.hζ hband (Nat.sub_le M 1)
  have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos hΛ1
  have hρ : 0 < c.D.termRho cr M := by
    unfold OCData.termRho OCData.termB
    have h1 : 0 < cr := by rw [x.one]; exact one_pos
    exact mul_pos h1 (Real.sqrt_pos.2 (mul_pos hν hh))
  have hρ' : c.D.termRho cr M ≤ c.D.eps (c.Gt'.level - 1) := by
    rw [hlev]
    exact hρε.trans (EntryScales.epsilon_antitone (by rw [hq]; exact X.hq.1)
      (by rw [hΛD]; exact hΛ) (Nat.sub_le (M - 1) 1))
  have hi : 1 ≤ c.Gt'.level := by omega
  have hj' : j₀ ≤ c.Gt'.level := by omega
  have hε : 0 < c.D.eps (c.Gt'.level - 1) := by rw [hlev]; exact hεpos
  intro i j α d
  refine ⟨native_physCoeff_joint_measurable_of_context x.cert hST hnat hΛ1 hi hj' hb hε c.tp
    (c.a + A.T₀) hres hres2 i j α d.1, fun t _ => ?_, fun t _ => ?_, ?_⟩
  · exact (termCtx_physCoeff c x x.cert hST hSH hV hΛ hj hM2 _ i j α d.1 t).1
  · exact (termCtx_physCoeff c x x.cert hST hSH hV hΛ hj hM2 0 i j α d.1 t).2
  · exact native_physCoeff_all_order_seminorm_finite x.cert hST hnat hi hj' hb hε c.tp (c.a + A.T₀)
      i j α (hres i) (hres2 i) _ hρ hρ' _ d.1

/-- **(R), `FilterRegStatement`.** -/
theorem filterReg : FilterRegStatement := by
  intro X
  obtain ⟨Λc, hΛc, hcore⟩ := seedStruct_scales X
  refine ⟨max Λc 128, le_max_right _ _, fun A hΛ hV => ?_⟩
  have hΛc' : Λc ≤ A.Λ := le_trans (le_max_left _ _) hΛ
  have h128 : 128 ≤ A.Λ := le_trans (le_max_right _ _) hΛ
  refine ⟨0, fun kc _ => ?_⟩
  set S := max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 with hS
  refine ⟨S, S, 0, fun sXT sZT hX hZ Kout _ => ⟨0, fun Kw Lt nW hk₀w _ cr kS _ _ _ _ _
    hcr0 _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _ cP CP cHP Cw Ce cker _ Cfl => ?_⟩⟩
  obtain ⟨M₀, hM₀2, hM₀⟩ := hcore A.Λ hΛc' cr 0 0 0 hcr0 le_rfl le_rfl
  refine ⟨0, 1, 0, one_pos, 1, 1, le_rfl, one_pos, fun C _ j₀ hcar => ?_⟩
  refine ⟨max M₀ (j₀ + 2), fun M hM c x => ?_⟩
  have hMM : M₀ ≤ M := le_trans (le_max_left _ _) hM
  have hMj : j₀ + 2 ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, -⟩ := c.data
  exact filterRegAt c x kc hV h128 le_rfl le_rfl hcar hX hZ (by omega) (by omega)
    (hM₀ M hMM c.D hDα hDq hDΛ hband).2.1

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! **The kernel widths and record lengths of ALL identities of the terminal successor.**

`retained_width_length` states the widths for the retained family; its proof first proves
the statement for every identity of `Gt'`. Here that statement is exported, together with the
width `r_w = termRW` of every identity with a seed kernel.

Degenerate cases: an empty stage; a stage without seed-kernel identities.
-/

theorem width_all {X : TermConstruction} {A : TermArgs X} {sXT sZT : ℕ} {nW : ℕ+}
    {cr CL Cχ : ℝ} {kW : InvConsts} {cP CP cH Cw : ℝ} {j₀ M : ℕ} {D : OCData} {a : ℝ}
    {lawW : BirthLaw} {PW : ProvParams} {Gw : GenStage D ScalarH A.Dt A.bw j₀} {aM tp : ℝ}
    {lawT : BirthLaw} {Gt' : GenStage D ScalarH A.Dt A.bw j₀}
    (hctx : TermPassCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt')
    (hq1 : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (hCL : CL * D.eps (M + 1) ≤ D.eps (M - 1)) (hρ : D.termRho cr M ≤ D.eps (M - 1 - 1)) :
    ∀ v u (γ : Gt'.fam.Γ v u),
      (Gt'.kernelOf (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr) v u γ).width =
        (Gt'.fam.identity v u γ).record.width ∧
      (Gt'.fam.identity v u γ).record.length ≤ D.eps (M - 1 - 1) ∧
      (IsSeedKernel (A.Pt D Cw cr M) Gt' v u γ →
        (Gt'.fam.identity v u γ).record.width = D.termRW A.σw M) ∧
      (¬ IsSeedKernel (A.Pt D Cw cr M) Gt' v u γ →
        (Gt'.fam.identity v u γ).record.width = D.termRNew cr A.tT M) := by
  obtain ⟨hdata, hweak, -, -, -, -, hsucc⟩ := hctx
  obtain ⟨-, -, hlev, -, hbirths, ⟨hseedprov, -, -⟩, hrec, -, -, hinv⟩ := hweak
  obtain ⟨-, htags, -⟩ := hinv
  obtain ⟨-, -, -, -, hHT, -, e, Cc, Cc0, -, -, hprov⟩ := hsucc
  have he1 : D.eps (M - 1) ≤ D.eps (M - 1 - 1) :=
    EntryScales.epsilon_antitone hq1 hΛ (Nat.sub_le (M - 1) 1)
  have hgood : ∀ v u (γ : Gw.fam.Γ v u),
      GoodTag (termKW D A.σw cr A.tT M) (D.eps (M - 1 - 1)) ((Gw.prov v u γ).tags (A.Pt D Cw cr M)) := by
    intro v u γ
    obtain ⟨k, tag, hk⟩ := hseedprov v u γ
    have hm := (htags v u γ).1
    obtain ⟨-, hw, hl, -⟩ := hrec v u γ
    rw [hk] at hm ⊢
    simp only [Prov.tags, ProvTags.Matches] at hm
    obtain ⟨-, -, -, hlen, hwid, -⟩ := hm
    refine ⟨?_, ?_⟩
    · show D.termRW A.σw M = tag.width
      rw [← hwid, hw]
    · show tag.length ≤ D.eps (M - 1 - 1)
      rw [← hlen]
      exact hl.trans (hCL.trans he1)
  intro v' u' γ'
  have hm := (hHT v' u' γ').1
  obtain ⟨hprv, -⟩ := hprov v' u' γ'
  have hg := succSource_tags_good (A.Pt D Cw cr M) (kw := termKW D A.σw cr A.tT M)
    (L := D.eps (M - 1 - 1)) hgood (fun b => rfl) (fun b => hρ) Gw.level (e v' u' γ').1
  rw [← hprv] at hg
  obtain ⟨-, -, -, hlen, hwid, -⟩ := hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold GenStage.kernelOf
    obtain ⟨hg1, -⟩ := hg
    rw [hwid]
    generalize ((Gt'.prov v' u' γ').tags (A.Pt D Cw cr M)).kernel = key at hg1 ⊢
    cases key
    · exact hg1
    · exact hg1
  · rw [hlen]; exact hg.2
  · rintro ⟨k, hk⟩
    have hg1 := hg.1
    rw [hk] at hg1
    rw [hwid]
    exact hg1.symm
  · intro hns
    cases hk : ((Gt'.prov v' u' γ').tags (A.Pt D Cw cr M)).kernel with
    | seed k => exact absurd ⟨k, hk⟩ hns
    | fresh b =>
      have hg1 := hg.1
      rw [hk] at hg1
      rw [hwid]
      exact hg1.symm

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! **The per-identity kernel price of ALL identities of the terminal successor.**

`retainedPrice_ctx` states the uniform identity price for the retained family. Here it is
proved for every identity of `Gt'` at a `TermResCtx`: the slot transversality, naturality,
reserves, certificate and the scale facts are those of `Gt'` itself (all its components have grade
at most one), and the record length bound holds for every identity (`width_all`).

Degenerate cases: order `kk = 0`; `A_k = 0` (then every coefficient seminorm sum vanishes).
-/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The passage context of a `TermResCtx`. -/
theorem passCtx
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) :
    TermPassCtx A sXT sZT nW cr CL Cχ kW cP CP cHP Cw M c.D c.a c.lawW c.PW c.Gw c.aM c.tp
      c.lawT c.Gt' :=
  ⟨c.data, c.weak, c.prep.1, c.prep.2.1, c.prep.2.2.1, c.law, c.succ⟩

/-- **The identity price of every identity of `Gt'`.** -/
theorem price_all
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) {CH Υ : ℝ} (hV : A.Valid) (hΛ : 128 ≤ A.Λ)
    (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ) (hcar : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀)
    (hX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT)
    (hj : j₀ + 1 ≤ M) (hM2 : 2 ≤ M) (hρε : c.D.termRho cr M ≤ c.D.eps (M - 1))
    (hCL : CL * c.D.eps (M + 1) ≤ c.D.eps (M - 1))
    (kk : ℕ) (cc : ℕ → ℝ) (Ak : ℝ) (m₀ : ℕ) (hm₀ : m₀ + 2 ≤ M)
    (hu : UnifPriceAt X.α X.q A.Λ X.ζ A.bw kk A.Dt cc Ak m₀) :
    ∀ v u (γ : c.Gt'.fam.Γ v u),
      (∑ d : ↥(Finset.Icc 2 A.Dt),
        (coefficientSeminorm (c.D.termRho cr M) kk c.tp (c.a + A.T₀)
          (c.Gt'.physCoeff v u γ d.1)).toReal * cc (d.1 - 2) /
          (c.D.κ (M - 1) * (c.Gt'.fam.identity v u γ).record.width ^ (d.1 - 2))) ≤
        Ak * (‖(c.Gt'.fam.identity v u γ).map‖ * (c.Gt'.fam.identity v u γ).record.size *
          constituentPrice (c.Gt'.fam.identity v u γ).record) := by
  have hb : 0 < A.bw := hV.2.2.1.1
  have hST := termCtx_slotTransverse c x hV hΛ hCH hΥ hcar hX hZ
  obtain ⟨hα, hq, hΛD, hζD, hseq, hband, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := by rw [hΛD]; omega
  have hΛ128 : 128 ≤ c.D.Λ := by rw [hΛD]; exact hΛ
  have hq1 : 1 < c.D.q := by rw [hq]; exact X.hq.1
  have hlevW : c.Gw.level = M := c.weak.2.2.1
  have hbirth : ∀ w : CompIn c.Gw.comps, w.1.births = [] := c.weak.2.2.2.2.1
  have hlev : c.Gt'.level = M - 1 := by rw [c.succ.2.1, hlevW]
  have hres : ∀ w : CompIn c.Gt'.comps, 0 ≤ compReserve kW w.1 := fun w =>
    termReserve_nonneg x.reserve1
      (termGrade_le_one (fun u => by simp [compGrade, hbirth u]) c.succ w)
  have hres2 : ∀ w : CompIn c.Gt'.comps, compReserve kW w.1 ≤ 2 := fun w =>
    (AVRegularity.Providers.CascadeInvariants.compReserve_le_one kW w.1).trans (by norm_num)
  have hnat := c.succ.2.2.2.1
  have hεpos : 0 < c.D.eps (M - 1 - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hν : 0 < c.D.κ (M - 1) :=
    CycleReference.bandChain_pos (by omega : 1 ≤ A.Λ) X.hζ hband (Nat.sub_le M 1)
  have hρ0 : 0 < c.D.termRho cr M := by
    unfold OCData.termRho OCData.termB
    have h1 : 0 < cr := by rw [x.one]; exact one_pos
    have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos hΛ1
    exact mul_pos h1 (Real.sqrt_pos.2 (mul_pos hν hh))
  have hρ' : c.D.termRho cr M ≤ c.D.eps (c.Gt'.level - 1) := by
    rw [hlev]
    exact hρε.trans (EntryScales.epsilon_antitone hq1 hΛ128 (Nat.sub_le (M - 1) 1))
  have hρ2 : c.D.termRho cr M ≤ c.D.eps c.Gt'.level := by rw [hlev]; exact hρε
  have hWL := width_all (passCtx c) hq1 hΛ128 hCL (by
    rw [← hlev]; exact hρ')
  have hkap : c.D.kap c.Gt'.level = c.D.κ (M - 1) := by
    unfold OCData.kap
    rw [hlev, Nat.min_eq_left (by rw [hterm]; omega)]
  have hν' : 0 < c.D.kap c.Gt'.level := by rw [hkap]; exact hν
  intro v u γ
  have hlen : 3 ≤ (c.Gt'.fam.identity v u γ).maxOrder →
      (c.Gt'.fam.identity v u γ).record.length ≤ c.D.eps (c.Gt'.level - 1) := fun _ =>
    le_of_le_of_eq (hWL v u γ).2.1 (by rw [hlev])
  have hsum := hu c.D hα hq hΛD hζD hseq j₀ _ c.Gt' kW x.cert hnat
    (by rw [hlev]; omega) (by rw [hlev]; omega) (by rw [hlev]; omega)
    (by rw [hlev]; exact hεpos) (by rw [hlev]; exact Construction.Stream.ocEpsilon_pos hΛ1)
    hν' hST c.tp (c.a + A.T₀) v u γ (hres v) (hres2 v)
    (c.D.termRho cr M) hρ0 hρ' hρ2 hlen
  rw [hkap] at hsum
  exact hsum

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.Construction.Preservation.Ledger
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! **The weak-price Schur bound at one terminal context.**

At a `TermResCtx`, the kernel Schur matrix of the coefficients of the identities of `Gt'` with a
seed kernel and a root in `Gw` (width `r_w = termRW`, radius `ρ`, masses of `Gt'`) has Schur bound
`A_k |W+1| (4 C_w S)`, with `S = max(C_χ ε_M^{χ_w}, 0)` the weak ledger and `A_k` the constant of
the uniform identity price. The proof is `kernel_schur_of_identity_prices` with the price of every
identity of `Gt'` (`price_all`) and the copy-only masked Schur bound
(`masked_copy_schur`); a seed-kernel identity has a copy source because letters carry a
fresh kernel.

Degenerate cases: `C_w = 0` (the bound is `0`; the seed-kernel part vanishes); no seed edges.
-/

section
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- A seed-kernel edge has a copy source. -/
theorem seed_copy {P : ProvParams} {Mn : SuccMenu} {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    {G G' : GenStage D ScalarH Dm b j₀} (E : ActualSources P Mn G G')
    (hEprov : ∀ e : LedgerEdge G', G'.prov e.1 e.2.1 e.2.2 = (E.source e).prov G.level)
    (e : LedgerEdge G') (hk : IsSeedKernel P G' e.1 e.2.1 e.2.2) : (E.source e).letter? = none := by
  obtain ⟨k, hk⟩ := hk
  rw [hEprov e] at hk
  cases hs : E.source e <;> simp_all [SuccSource.prov, Prov.tags, SuccSource.letter?]

/-- **The weak-price Schur bound at a context.** -/
theorem schurW_at
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) {CH Υ : ℝ} (hV : A.Valid) (hΛ : 128 ≤ A.Λ)
    (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ) (hcar : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀)
    (hX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT)
    (hj : j₀ + 1 ≤ M) (hM2 : 2 ≤ M) (hρε : c.D.termRho cr M ≤ c.D.eps (M - 1))
    (hCL : CL * c.D.eps (M + 1) ≤ c.D.eps (M - 1)) (hCw : 0 ≤ Cw)
    (kc : ℕ) (Ak : ℝ) (m₀ : ℕ) (hm₀ : m₀ + 2 ≤ M) (hAk : 0 ≤ Ak)
    (hu : UnifPriceAt X.α X.q A.Λ X.ζ A.bw (kc + 2 * A.pT) A.Dt (fun _ => 1) Ak m₀)
    (hF1 : 1 ≤ birthDiagonalFactor c.D.q c.D.Λ M c.lawT false)
    (hS : max (Cχ * c.D.eps M ^ A.χw) 0 ≤ 1 / 2) :
    SchurBound (Ak * (((insert [] (wordsUpTo A.alph (A.RT + 1))).card : ℝ) *
        (4 * Cw * max (Cχ * c.D.eps M ^ A.χw) 0)))
      (kernelSchurMatrix (G := fun _ j _ => ScalarH j.1.root) (c.D.κ (M - 1))
        (c.D.termRho cr M) (c.Gt'.mass c.lawT) (kc + 2 * A.pT) A.Dt c.tp (c.a + A.T₀)
        (fun _ => 1) (fun _ _ _ => c.D.termRW A.σw M)
        (fun _ j _ => ContinuousLinearMap.id ℝ (ScalarH j.1.root))
        (filtCoeff c.Gt' (filterEdgeW c))) := by
  classical
  have hprice := price_all c x hV hΛ hCH hΥ hcar hX hZ hj hM2 hρε hCL (kc + 2 * A.pT)
    (fun _ => 1) Ak m₀ hm₀ hu
  obtain ⟨hα, hq, hΛD, hζD, hseq, hband, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := by rw [hΛD]; omega
  have hΛ128 : 128 ≤ c.D.Λ := by rw [hΛD]; exact hΛ
  have hq1 : 1 < c.D.q := by rw [hq]; exact X.hq.1
  have hν : 0 < c.D.κ (M - 1) :=
    CycleReference.bandChain_pos (by omega : 1 ≤ A.Λ) X.hζ hband (Nat.sub_le M 1)
  have hWL := width_all (passCtx c) hq1 hΛ128 hCL (by
    exact hρε.trans (EntryScales.epsilon_antitone hq1 hΛ128 (Nat.sub_le (M - 1) 1)))
  obtain ⟨-, -, hlev, -, hbirths, ⟨hseedprov, -, -⟩, -, -, -, hinv⟩ := c.weak
  obtain ⟨hmass, -, -, hiota, -, hetaB, -⟩ := c.law
  obtain ⟨-, htags, -, -, -, -, -, hled, -⟩ := hinv
  obtain ⟨-, -, -, -, -, hsched, -⟩ := hV
  obtain ⟨-, -, -, -, -, -, -, -, htT, -⟩ := hsched
  have hPeq : A.Pt c.D Cw cr M = genProvParams c.D Cw A.η₀ A.NT A.pT
      (fun _ => c.D.termRho cr M) (fun _ => c.D.termRNew cr A.tT M) :=
    termProvParams_eq_gen c.D Cw cr A.tT A.η₀ A.NT A.pT M
  have hsucc := c.succ
  rw [hPeq] at hsucc
  have hG : c.Gw.HasTags (genProvParams c.D Cw A.η₀ A.NT A.pT
      (fun _ => c.D.termRho cr M) (fun _ => c.D.termRNew cr A.tT M)) :=
    hasTags_of_seed_prov hseedprov htags
  have hold : ∀ v ∈ c.Gw.comps, ∀ e ∈ v.births, c.Gw.level ≤ e.scale := by
    intro v hv e he
    have h0 : v.births = [] := hbirths ⟨v, hv⟩
    rw [h0] at he
    exact absurd he (by simp)
  have hrb : (fun _ => c.D.termRNew cr A.tT M) (c.Gw.level - 1) =
      (fun _ => c.D.termRho cr M) (c.Gw.level - 1) * c.D.eps (c.Gw.level - 1) ^ A.tT := by
    rw [hlev]; rfl
  have hled' : markedLedger (c.Gw.mass c.lawT) (c.Gw.marker c.lawT) c.Gw.fam ≤
      max (Cχ * c.D.eps M ^ A.χw) 0 :=
    (weak_ledger_lawT hbirths hmass hled).trans (le_max_left _ _)
  obtain ⟨E, hEprov⟩ := sources hsucc
  have hmask : ∀ e : LedgerEdge c.Gt', (e.2.1.1 ∈ c.Gw.comps ∧
      IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' e.1 e.2.1 e.2.2) → (E.source e).letter? = none :=
    fun e he => seed_copy E hEprov e he.2
  have hm := masked_copy_schur (G := c.Gw) (G' := c.Gt')
    (Mn := A.Mt M sXT sZT c.tp cr) hq1 hΛ128 hCw htT.le hrb
    (fun l hl => termFresh_letters l hl) c.lawT (by rw [hlev]; exact hF1) hG
    (fun v hv e he => hold v hv e he) hsucc E
    (fun e => e.2.1.1 ∈ c.Gw.comps ∧ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' e.1 e.2.1 e.2.2)
    hmask (le_max_right _ _) hS ((le_max_left _ _).trans hled')
  have hpm : ∀ (v u : CompIn c.Gt'.comps) (γ : c.Gt'.fam.Γ v u),
      (if (u.1 ∈ c.Gw.comps ∧ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' v u γ) then
        identityPrice c.Gt' (ledgerDiagonal c.D.q c.D.Λ c.lawT false) ⟨v, u, γ⟩ else 0) =
      Real.sqrt (c.Gt'.mass c.lawT u / c.Gt'.mass c.lawT v) *
        (if (u.1 ∈ c.Gw.comps ∧ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' v u γ) then
          ‖(c.Gt'.fam.identity v u γ).map‖ * (c.Gt'.fam.identity v u γ).record.size *
            constituentPrice (c.Gt'.fam.identity v u γ).record else 0) := by
    intro v u γ
    by_cases h : (u.1 ∈ c.Gw.comps ∧ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' v u γ)
    · simp only [h, and_self, ↓reduceIte]
      unfold identityPrice
      rw [ledgerDiagonal_ratio hq1 hΛ128]
      simp [ledgerMarker, GenStage.mass]
    · simp only [h, ↓reduceIte, mul_zero]
  have hbud : SchurBound (((insert [] (wordsUpTo (A.Mt M sXT sZT c.tp cr).A
        ((A.Mt M sXT sZT c.tp cr).J + 1))).card : ℝ) * (4 * Cw * max (Cχ * c.D.eps M ^ A.χw) 0))
      (fun i j : CompIn c.Gt'.comps => Real.sqrt (c.Gt'.mass c.lawT j / c.Gt'.mass c.lawT i) *
        ∑ γ : c.Gt'.fam.Γ i j, (if (j.1 ∈ c.Gw.comps ∧
          IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' i j γ) then
          ‖(c.Gt'.fam.identity i j γ).map‖ * (c.Gt'.fam.identity i j γ).record.size *
            constituentPrice (c.Gt'.fam.identity i j γ).record else 0)) := by
    have hfun : (fun i j : CompIn c.Gt'.comps => Real.sqrt (c.Gt'.mass c.lawT j / c.Gt'.mass c.lawT i) *
        ∑ γ : c.Gt'.fam.Γ i j, (if (j.1 ∈ c.Gw.comps ∧
          IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' i j γ) then
          ‖(c.Gt'.fam.identity i j γ).map‖ * (c.Gt'.fam.identity i j γ).record.size *
            constituentPrice (c.Gt'.fam.identity i j γ).record else 0)) =
        fun v u => ∑ γ, (if (u.1 ∈ c.Gw.comps ∧ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' v u γ) then
          identityPrice c.Gt' (ledgerDiagonal c.D.q c.D.Λ c.lawT false) ⟨v, u, γ⟩ else 0) := by
      funext v u
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun γ _ => (hpm v u γ).symm
    rw [hfun]
    convert hm
  have hrpos : ∀ (i j : CompIn c.Gt'.comps) (γ : c.Gt'.fam.Γ i j), 0 < c.D.termRW A.σw M := by
    intro i j γ
    have hε : 0 < c.D.eps M := Construction.Stream.ocEpsilon_pos hΛ1
    unfold OCData.termRW
    positivity
  have hk := AVRegularity.Construction.StageKernelPrice.kernel_schur_of_identity_prices
    (ι := CompIn c.Gt'.comps) (h := fun v => ScalarH v.1.root)
    (Γ := c.Gt'.fam.Γ) (G := fun _ j _ => ScalarH j.1.root)
    (c.D.κ (M - 1)) (c.D.termRho cr M) (fun v => c.Gt'.mass c.lawT v) (kc + 2 * A.pT) A.Dt
    c.tp (c.a + A.T₀) (fun _ => 1) (fun _ _ _ => c.D.termRW A.σw M)
    (fun _ j _ => ContinuousLinearMap.id ℝ (ScalarH j.1.root))
    (filtCoeff c.Gt' (filterEdgeW c))
    (fun v u γ => if (u.1 ∈ c.Gw.comps ∧ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' v u γ) then
          ‖(c.Gt'.fam.identity v u γ).map‖ * (c.Gt'.fam.identity v u γ).record.size *
            constituentPrice (c.Gt'.fam.identity v u γ).record else 0)
    Ak _ hν hrpos (fun _ _ => zero_le_one) (fun _ _ _ => ContinuousLinearMap.norm_id_le) hAk
    (fun v u γ => by
      by_cases h : (u.1 ∈ c.Gw.comps ∧ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' v u γ)
      · have h1 := hprice v u γ
        rw [(hWL v u γ).2.2.1 h.2] at h1
        simpa only [filtCoeff, filterEdgeW, h, and_self, ↓reduceIte] using h1
      · simp [filtCoeff, filterEdgeW, h, CycleComparison.Coarse.coefficientSeminorm_zero_coefficient])
    hbud
  exact hk
end

/-! **The fresh-price Schur bound at one terminal context.**

At a `TermResCtx`, the kernel Schur matrix of the coefficients of the identities of `Gt'` with a
fresh kernel and a root in `Gw` (width `r_new = termRNew`, radius `ρ`, masses of `Gt'`) has Schur
bound `A_k |W+1| · 2 |A| C_w · R` with `R = (1 + √(|𝔚|/c_H)) ε_{M-1}^{b_T}` the fresh-letter
prefactor. This is the same route as the weak price, with the mass weight directly: the diagonal
`a = ε_unmarked / √mass` of the unit-marker ledger gives `√(π_u/π_v)` and no conversion of the
mass/marker² weight is needed. A fresh-kernel edge has a letter source because every copy source of
the weak stage has a seed kernel (`copy_kernel_seed`).

Degenerate cases: `C_w = 0` (the bound is `0`); no letters (`A = ∅`).
-/

section
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- A non-seed-kernel edge has a letter source. -/
theorem fresh_letter {P : ProvParams} {Mn : SuccMenu} {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    {G G' : GenStage D ScalarH Dm b j₀} (E : ActualSources P Mn G G')
    (hEprov : ∀ e : LedgerEdge G', G'.prov e.1 e.2.1 e.2.2 = (E.source e).prov G.level)
    (hseed : ∀ v u (γ : G.fam.Γ v u), ∃ k tag, G.prov v u γ = .seed k tag)
    (e : LedgerEdge G') (hk : ¬ IsSeedKernel P G' e.1 e.2.1 e.2.2) : (E.source e).letter? ≠ none := by
  intro hnone
  obtain ⟨k, hk'⟩ := copy_kernel_seed P hseed G.level (E.source e) (E.valid e) hnone
  exact hk ⟨k, by rw [hEprov e]; exact hk'⟩

/-- **The fresh-price Schur bound at a context.** -/
theorem schurF_at
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) {CH Υ : ℝ} (hV : A.Valid) (hΛ : 128 ≤ A.Λ)
    (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ) (hcar : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀)
    (hX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT)
    (hj : j₀ + 1 ≤ M) (hM2 : 2 ≤ M) (hρε : c.D.termRho cr M ≤ c.D.eps (M - 1))
    (hCL : CL * c.D.eps (M + 1) ≤ c.D.eps (M - 1)) (hCw : 0 ≤ Cw)
    (kc : ℕ) (Ak : ℝ) (m₀ : ℕ) (hm₀ : m₀ + 2 ≤ M) (hAk : 0 ≤ Ak)
    (hu : UnifPriceAt X.α X.q A.Λ X.ζ A.bw (kc + 2 * A.pT) A.Dt (fun _ => 1) Ak m₀)
    (hF1 : 1 ≤ birthDiagonalFactor c.D.q c.D.Λ M c.lawT false)
    (hS : max (Cχ * c.D.eps M ^ A.χw) 0 ≤ 1 / 2) :
    SchurBound (Ak * (((insert [] (wordsUpTo A.alph (A.RT + 1))).card : ℝ) *
        (2 * (A.alph.card : ℝ) * Cw *
          ((1 + Real.sqrt ((c.lawT.wordCount : ℝ) / c.lawT.cH)) *
            c.D.eps (M - 1) ^ (ocDelta c.D.α c.D.q - A.η₀ - A.η₀ / 4 -
              A.tT * (termExcess A.NT A.pT A.alph : ℝ))))))
      (kernelSchurMatrix (G := fun _ j _ => ScalarH j.1.root) (c.D.κ (M - 1))
        (c.D.termRho cr M) (c.Gt'.mass c.lawT) (kc + 2 * A.pT) A.Dt c.tp (c.a + A.T₀)
        (fun _ => 1) (fun _ _ _ => c.D.termRNew cr A.tT M)
        (fun _ j _ => ContinuousLinearMap.id ℝ (ScalarH j.1.root))
        (filtCoeff c.Gt' (filterEdgeF c))) := by
  classical
  have hprice := price_all c x hV hΛ hCH hΥ hcar hX hZ hj hM2 hρε hCL (kc + 2 * A.pT)
    (fun _ => 1) Ak m₀ hm₀ hu
  obtain ⟨hα, hq, hΛD, hζD, hseq, hband, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := by rw [hΛD]; omega
  have hΛ128 : 128 ≤ c.D.Λ := by rw [hΛD]; exact hΛ
  have hq1 : 1 < c.D.q := by rw [hq]; exact X.hq.1
  have hν : 0 < c.D.κ (M - 1) :=
    CycleReference.bandChain_pos (by omega : 1 ≤ A.Λ) X.hζ hband (Nat.sub_le M 1)
  have hWL := width_all (passCtx c) hq1 hΛ128 hCL (by
    exact hρε.trans (EntryScales.epsilon_antitone hq1 hΛ128 (Nat.sub_le (M - 1) 1)))
  have hρ0 : 0 < c.D.termRho cr M := by
    unfold OCData.termRho OCData.termB
    have h1 : 0 < cr := by rw [x.one]; exact one_pos
    have hh : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos hΛ1
    exact mul_pos h1 (Real.sqrt_pos.2 (mul_pos hν hh))
  obtain ⟨-, -, hlev, -, hbirths, ⟨hseedprov, -, -⟩, -, -, -, hinv⟩ := c.weak
  obtain ⟨hmass, -, -, hiota, -, hetaB, -⟩ := c.law
  obtain ⟨-, htags, -, -, -, -, -, hled, -⟩ := hinv
  obtain ⟨-, -, -, -, -, hsched, -⟩ := hV
  obtain ⟨-, -, -, -, -, -, -, -, htT, -⟩ := hsched
  have hPeq : A.Pt c.D Cw cr M = genProvParams c.D Cw A.η₀ A.NT A.pT
      (fun _ => c.D.termRho cr M) (fun _ => c.D.termRNew cr A.tT M) :=
    termProvParams_eq_gen c.D Cw cr A.tT A.η₀ A.NT A.pT M
  have hsucc := c.succ
  rw [hPeq] at hsucc
  have hG : c.Gw.HasTags (genProvParams c.D Cw A.η₀ A.NT A.pT
      (fun _ => c.D.termRho cr M) (fun _ => c.D.termRNew cr A.tT M)) :=
    hasTags_of_seed_prov hseedprov htags
  have hold : ∀ v ∈ c.Gw.comps, ∀ e ∈ v.births, c.Gw.level ≤ e.scale := by
    intro v hv e he
    have h0 : v.births = [] := hbirths ⟨v, hv⟩
    rw [h0] at he
    exact absurd he (by simp)
  have hrb : (fun _ => c.D.termRNew cr A.tT M) (c.Gw.level - 1) =
      (fun _ => c.D.termRho cr M) (c.Gw.level - 1) * c.D.eps (c.Gw.level - 1) ^ A.tT := by
    rw [hlev]; rfl
  have hbirth : birthDiagonalFactor c.D.q c.D.Λ M c.lawT false *
      c.D.eps (M - 1) ^ (ocDelta c.D.α c.D.q - A.η₀ -
        A.tT * (termExcess A.NT A.pT A.alph : ℝ)) ≤
      (1 + Real.sqrt ((c.lawT.wordCount : ℝ) / c.lawT.cH)) *
        c.D.eps (M - 1) ^ (ocDelta c.D.α c.D.q - A.η₀ - A.η₀ / 4 -
          A.tT * (termExcess A.NT A.pT A.alph : ℝ)) := by
    refine birth_bound_any hq1 hΛ128 c.lawT (by rw [hiota]) M ?_ false
    rw [hetaB, hiota]; ring
  have hled' : markedLedger (c.Gw.mass c.lawT) (c.Gw.marker c.lawT) c.Gw.fam ≤
      max (Cχ * c.D.eps M ^ A.χw) 0 :=
    (weak_ledger_lawT hbirths hmass hled).trans (le_max_left _ _)
  obtain ⟨E, hEprov⟩ := sources hsucc
  have hmask : ∀ e : LedgerEdge c.Gt', (e.2.1.1 ∈ c.Gw.comps ∧
      ¬ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' e.1 e.2.1 e.2.2) → (E.source e).letter? ≠ none :=
    fun e he => fresh_letter E hEprov hseedprov e he.2
  have hm := masked_letter_schur (G := c.Gw) (G' := c.Gt')
    (R := (1 + Real.sqrt ((c.lawT.wordCount : ℝ) / c.lawT.cH)) *
      c.D.eps (M - 1) ^ (ocDelta c.D.α c.D.q - A.η₀ - A.η₀ / 4 -
        A.tT * (termExcess A.NT A.pT A.alph : ℝ))) (Mn := A.Mt M sXT sZT c.tp cr) hq1 hΛ128 hCw htT.le hrb
    (fun l hl => termFresh_letters l hl) c.lawT (by rw [hlev]; exact hF1) (by
      rw [hlev]; exact hbirth) hG
    (fun v hv e he => hold v hv e he) hsucc E
    (fun e => e.2.1.1 ∈ c.Gw.comps ∧ ¬ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' e.1 e.2.1 e.2.2)
    hmask (le_max_right _ _) hS ((le_max_left _ _).trans hled')
  have hpm : ∀ (v u : CompIn c.Gt'.comps) (γ : c.Gt'.fam.Γ v u),
      (if (u.1 ∈ c.Gw.comps ∧ ¬ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' v u γ) then
        identityPrice c.Gt' (ledgerDiagonal c.D.q c.D.Λ c.lawT false) ⟨v, u, γ⟩ else 0) =
      Real.sqrt (c.Gt'.mass c.lawT u / c.Gt'.mass c.lawT v) *
        (if (u.1 ∈ c.Gw.comps ∧ ¬ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' v u γ) then
          ‖(c.Gt'.fam.identity v u γ).map‖ * (c.Gt'.fam.identity v u γ).record.size *
            constituentPrice (c.Gt'.fam.identity v u γ).record else 0) := by
    intro v u γ
    by_cases h : (u.1 ∈ c.Gw.comps ∧ ¬ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' v u γ)
    · simp only [h]
      unfold identityPrice
      rw [ledgerDiagonal_ratio hq1 hΛ128]
      simp [ledgerMarker, GenStage.mass]
    · simp only [h, ↓reduceIte, mul_zero]
  have hbud : SchurBound (((insert [] (wordsUpTo (A.Mt M sXT sZT c.tp cr).A
        ((A.Mt M sXT sZT c.tp cr).J + 1))).card : ℝ) *
        (2 * ((A.Mt M sXT sZT c.tp cr).A.card : ℝ) * Cw *
          ((1 + Real.sqrt ((c.lawT.wordCount : ℝ) / c.lawT.cH)) *
            c.D.eps (M - 1) ^ (ocDelta c.D.α c.D.q - A.η₀ - A.η₀ / 4 -
              A.tT * (termExcess A.NT A.pT A.alph : ℝ)))))
      (fun i j : CompIn c.Gt'.comps => Real.sqrt (c.Gt'.mass c.lawT j / c.Gt'.mass c.lawT i) *
        ∑ γ : c.Gt'.fam.Γ i j, (if (j.1 ∈ c.Gw.comps ∧
          ¬ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' i j γ) then
          ‖(c.Gt'.fam.identity i j γ).map‖ * (c.Gt'.fam.identity i j γ).record.size *
            constituentPrice (c.Gt'.fam.identity i j γ).record else 0)) := by
    have hfun : (fun i j : CompIn c.Gt'.comps => Real.sqrt (c.Gt'.mass c.lawT j / c.Gt'.mass c.lawT i) *
        ∑ γ : c.Gt'.fam.Γ i j, (if (j.1 ∈ c.Gw.comps ∧
          ¬ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' i j γ) then
          ‖(c.Gt'.fam.identity i j γ).map‖ * (c.Gt'.fam.identity i j γ).record.size *
            constituentPrice (c.Gt'.fam.identity i j γ).record else 0)) =
        fun v u => ∑ γ, (if (u.1 ∈ c.Gw.comps ∧
            ¬ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' v u γ) then
          identityPrice c.Gt' (ledgerDiagonal c.D.q c.D.Λ c.lawT false) ⟨v, u, γ⟩ else 0) := by
      funext v u
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun γ _ => (hpm v u γ).symm
    rw [hfun]
    convert hm
  have hrpos : ∀ (i j : CompIn c.Gt'.comps) (γ : c.Gt'.fam.Γ i j), 0 < c.D.termRNew cr A.tT M := by
    intro i j γ
    have hε : 0 < c.D.eps (M - 1) := Construction.Stream.ocEpsilon_pos hΛ1
    unfold OCData.termRNew
    positivity
  have hk := AVRegularity.Construction.StageKernelPrice.kernel_schur_of_identity_prices
    (ι := CompIn c.Gt'.comps) (h := fun v => ScalarH v.1.root)
    (Γ := c.Gt'.fam.Γ) (G := fun _ j _ => ScalarH j.1.root)
    (c.D.κ (M - 1)) (c.D.termRho cr M) (fun v => c.Gt'.mass c.lawT v) (kc + 2 * A.pT) A.Dt
    c.tp (c.a + A.T₀) (fun _ => 1) (fun _ _ _ => c.D.termRNew cr A.tT M)
    (fun _ j _ => ContinuousLinearMap.id ℝ (ScalarH j.1.root))
    (filtCoeff c.Gt' (filterEdgeF c))
    (fun v u γ => if (u.1 ∈ c.Gw.comps ∧ ¬ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' v u γ) then
          ‖(c.Gt'.fam.identity v u γ).map‖ * (c.Gt'.fam.identity v u γ).record.size *
            constituentPrice (c.Gt'.fam.identity v u γ).record else 0)
    Ak _ hν hrpos (fun _ _ => zero_le_one) (fun _ _ _ => ContinuousLinearMap.norm_id_le) hAk
    (fun v u γ => by
      by_cases h : (u.1 ∈ c.Gw.comps ∧ ¬ IsSeedKernel (A.Pt c.D Cw cr M) c.Gt' v u γ)
      · have h1 := hprice v u γ
        rw [(hWL v u γ).2.2.2 h.2] at h1
        have h' : filterEdgeF c v u γ := h
        simpa only [filtCoeff, h', h, not_false_eq_true, and_self, ↓reduceIte] using h1
      · have h' : ¬ filterEdgeF c v u γ := h
        simp [filtCoeff, h', h, CycleComparison.Coarse.coefficientSeminorm_zero_coefficient])
    hbud
  exact hk
end

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end
end
