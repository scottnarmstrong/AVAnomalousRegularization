-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.FluxProductionArithmetic
import AVRegularity.CycleDamping.TensorError
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.CycleComparison.Lift.SettingLiftSourceBlockCoefficient
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleResidualDifferentiated
public import AVRegularity.Statements.Intermediate.CycleOutput.PulseLiftData
public import AVRegularity.CycleComparison.LiftMeanEntrywise.Letter
import AVRegularity.CycleReference.TestDriftIntegrability

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Diagonal

/-! Source degree zero does not see the source edges (the term `𝒮_0 C_n` uses the preceding
source degree, so the grade-zero recursion involves `G`, `v` and `η` only). The grade-zero part of a
lift sequence of operator data `Q` (any depth `H`) is a lift sequence of depth `0` of the same data
with the edges removed, and a lift setting of `Q` gives a lift setting of depth `0` of the edge-free
data, with the reserves `q_s, q_f` recomputed at `H = 0` (every field of `IsLiftSetting` is monotone
in `q_s, q_f`). The shear `(par, V)` of the new setting is any presentation of the same drift. -/

section Data
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The operator data `Q` with every source edge removed. -/
def zeroEdgeData (Q : LiftOperatorData ι h D) : LiftOperatorData ι h D :=
  ⟨Q.η, Q.G, Q.v, fun _ _ _ => []⟩

theorem zeroEdgeData_edge (Q : LiftOperatorData ι h D) (v u : ι) (d : Finset.Icc 2 D) :
    (zeroEdgeData Q).edge v u d = [] := rfl

end Data

section Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The grade-zero recursion source depends on `η`, `G` and `v` only. -/
theorem liftA_gradeZero_congr (Q Q' : LiftOperatorData ι h D) (hη : Q'.η = Q.η)
    (hG : Q'.G = Q.G) (hv : Q'.v = Q.v) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (n : ℕ) :
    liftA Q' Cc a 0 n = liftA Q Cc a 0 n := by
  funext t X z
  unfold liftA
  rw [hη, hG, hv]
  simp

/-- The grade-zero mean operator depends on `η`, `G` and `v` only. -/
theorem liftMean_gradeZero_congr (Q Q' : LiftOperatorData ι h D) (hη : Q'.η = Q.η)
    (hG : Q'.G = Q.G) (hv : Q'.v = Q.v) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (n : ℕ) :
    liftMean Q' Cc a 0 n = liftMean Q Cc a 0 n := by
  funext t X
  simp only [liftMean, liftA_gradeZero_congr Q Q' hη hG hv Cc a n]

/-- The grade-zero centered cell source depends on `η`, `G` and `v` only. -/
theorem liftCellSource_gradeZero_congr (Q Q' : LiftOperatorData ι h D) (hη : Q'.η = Q.η)
    (hG : Q'.G = Q.G) (hv : Q'.v = Q.v) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (n : ℕ) :
    liftCellSource Q' Cc a 0 n = liftCellSource Q Cc a 0 n := by
  have ha := liftA_gradeZero_congr Q Q' hη hG hv Cc a n
  have hm : ∀ m, liftMean Q' Cc a 0 m = liftMean Q Cc a 0 m :=
    fun m => liftMean_gradeZero_congr Q Q' hη hG hv Cc a m
  funext t X z
  have hsum : (∑ j ∈ Finset.Icc 1 (n - 2),
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (0 : ℕ),
        liftApply j (Cc p.1 j) (liftMean Q' Cc a p.2 (n - j)) t X z) =
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (0 : ℕ),
        liftApply j (Cc p.1 j) (liftMean Q Cc a p.2 (n - j)) t X z := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro p hp
    have hp2 : p.2 = 0 := by
      have hpa := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      omega
    rw [hp2, hm]
  simp only [liftCellSource, ha, hm, hsum]

theorem liftCellSource_zeroEdge (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (n : ℕ) :
    liftCellSource (zeroEdgeData Q) Cc a 0 n = liftCellSource Q Cc a 0 n :=
  liftCellSource_gradeZero_congr Q (zeroEdgeData Q) rfl rfl rfl Cc a n

/-- The grade-zero part of a lift sequence of `Q` is a lift sequence of depth `0` of the
edge-free data. -/
theorem isLiftSequence_zeroEdge [∀ i, FiniteDimensional ℝ (h i)]
    (Q : LiftOperatorData ι h D) (sX sZ : ℕ) (t₀ t₁ : ℝ) (N H : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) :
    IsLiftSequence (zeroEdgeData Q) sX sZ t₀ t₁ N 0 Cc := by
  refine ⟨hseq.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hh h1 h0
    exfalso
    omega
  · intro hh hhh
    exact hseq.2.2.1 hh (hhh.trans (Nat.zero_le H))
  · intro hh hhh
    exact hseq.2.2.2.1 hh (hhh.trans (Nat.zero_le H))
  · intro hh hhh
    exact hseq.2.2.2.2.1 hh (hhh.trans (Nat.zero_le H))
  · intro hh hhh
    exact hseq.2.2.2.2.2.1 hh (hhh.trans (Nat.zero_le H))
  · intro hh hhh n hn hnN a₀ ha₀ X
    obtain rfl : hh = 0 := Nat.le_zero.mp hhh
    rw [liftCellSource_zeroEdge]
    exact hseq.2.2.2.2.2.2 0 (Nat.zero_le H) n hn hnN a₀ ha₀ X

end Lift

section Setting
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {bm : ι → ι → ℝ} {Θ : ℝ}

/-- The slow reserve at depth `0` is at most the slow reserve at depth `H`. -/
theorem zeroEdge_qs_le
    (P : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bm Θ)
    {qs' : ℕ} (hqs' : qs' = K + 4 * (0 + 1) * (N + D) ^ 2) : qs' ≤ qs := by
  rw [hqs', P.qs_eq]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_left 4 (Nat.add_le_add_right (Nat.zero_le H) 1))) K

/-- The fast reserve at depth `0` is at most the fast reserve at depth `H`. -/
theorem zeroEdge_qf_le
    (P : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bm Θ)
    {qf' : ℕ} (hqf' : qf' = max k (L + 2) + 0 * D + 2 * N + 2 * D) : qf' ≤ qf := by
  rw [hqf', P.qf_eq]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_right D (Nat.zero_le H)) _) _) _

/-- A lift setting of `Q` gives a lift setting of depth `0` of the edge-free data, for any shear
presentation `(par', V')` of the same drift. -/
theorem isLiftSetting_zeroEdge
    (P : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bm Θ)
    (par' : Fin 2) (V' : ℝ → ℝ → ℝ)
    (hshear : ∀ t z, Q.v t z = V' t (z par'.rev) • basisVec par')
    (hsmooth : ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (⊤ : ℕ∞) (V' t))
    (hper : ∀ t ∈ Set.Icc t₀ t₁, Function.Periodic (V' t) 1)
    (hmean : ∀ t ∈ Set.Icc t₀ t₁, ∫ s in (0 : ℝ)..1, V' t s = 0)
    {qs' qf' : ℕ} (hqs' : qs' = K + 4 * (0 + 1) * (N + D) ^ 2)
    (hqf' : qf' = max k (L + 2) + 0 * D + 2 * N + 2 * D) :
    IsLiftSetting (zeroEdgeData Q) π t₀ t₁ e ν B ρ E ℓ dstar εc lam par' V' 0 N K k L qs' qf'
      CG Cw Cj bm Θ := by
  have hqs : qs' ≤ qs := zeroEdge_qs_le P hqs'
  have hqf : qf' ≤ qf := zeroEdge_qf_le P hqf'
  have hdepth : HasDepthAtMost (zeroEdgeData Q).edge 0 := by
    intro _
    exact ⟨0, fun _ => rfl⟩
  have henv : IsScaledJetEnvelope π (zeroEdgeData Q).edge (Set.Icc t₀ t₁) lam Cj qs' qf' bm Θ :=
    { nonneg := P.envelope.nonneg
      row_sum := P.envelope.row_sum
      col_sum := P.envelope.col_sum
      jets := fun _ _ _ _ _ _ => by simp [zeroEdgeData_edge] }
  exact
    { window := P.window
      e_pos := P.e_pos
      ν_pos := P.ν_pos
      B_pos := P.B_pos
      ρ_pos := P.ρ_pos
      E_pos := P.E_pos
      ℓ_eq := P.ℓ_eq
      η_eq := P.η_eq
      η_le := P.η_le
      dstar_eq := P.dstar_eq
      εc_eq := P.εc_eq
      εc_le := P.εc_le
      lam_eq := P.lam_eq
      lam_le := P.lam_le
      N_ge := P.N_ge
      D_ge := P.D_ge
      qs_eq := hqs'
      qf_eq := hqf'
      mass_pos := P.mass_pos
      G_symm := P.G_symm
      G_meas := P.G_meas
      G_smooth := fun t ht i j => (P.G_smooth t ht i j).of_le (by exact_mod_cast hqs)
      G_ellip := P.G_ellip
      G_jets := fun r hr => P.G_jets r (hr.trans hqs)
      v_shear := hshear
      V_smooth := fun t ht => (hsmooth t ht).of_le (WithTop.coe_le_coe.mpr le_top)
      V_per := hper
      V_mean := hmean
      v_meas := P.v_meas
      w_jets := fun q hq => P.w_jets q (hq.trans hqf)
      depth := hdepth
      transverse := fun _ _ _ _ hγ => (List.not_mem_nil hγ).elim
      coeff_meas := fun _ _ _ _ hγ => (List.not_mem_nil hγ).elim
      coeff_smooth := fun _ _ _ _ hγ => (List.not_mem_nil hγ).elim
      envelope := henv }

end Setting

end AVRegularity.CycleComparison.Diagonal
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleComparison.Diagonal

/-! The finite-past transverse response of a unit-frequency cosine source with the flat cell
metric (on pulse `j` the flat zero-past solution is `χ_{I,j} = -(√η/e) M_j 𝐮_j`). With metric weight
`1`, the response to the source `r(s) cos(2πx)` is `m(t) cos(2πx)`, where
`m(t) = ∫_a^t e^{-4π²(t-s)} r(s) ds` is the zero-start memory of the mode (`cosineMemory`). The
proof reads the two Fourier coefficients `±1` of the cosine (`cosineCoeff`) off the literal profile
series of `profileCellResponse`. -/

open AVRegularity.CycleComparison.Lift

/-! ### The Fourier coefficients of the cosine -/

/-- The Fourier coefficients of `x ↦ cos 2πx`: `1/2` at `n = ±1`, zero otherwise. -/
def cosineCoeff (n : ℤ) : ℂ := if n = 1 ∨ n = -1 then 1 / 2 else 0

theorem cosineCoeff_of_not (n : ℤ) (hn : ¬(n = 1 ∨ n = -1)) : cosineCoeff n = 0 := by
  unfold cosineCoeff
  exact ite_eq_right hn

theorem cosineCoeff_one : cosineCoeff 1 = 1 / 2 := by
  unfold cosineCoeff
  exact ite_eq_left (Or.inl rfl)

theorem cosineCoeff_neg_one : cosineCoeff (-1) = 1 / 2 := by
  unfold cosineCoeff
  exact ite_eq_left (Or.inr rfl)

theorem cosineCoeff_eq_zero_of_not_mem (n : ℤ) (hn : n ∉ ({1, -1} : Finset ℤ)) :
    cosineCoeff n = 0 := by
  apply cosineCoeff_of_not
  rintro (rfl | rfl) <;> simp at hn

theorem summable_cosineCoeff : Summable cosineCoeff :=
  summable_of_ne_finset_zero cosineCoeff_eq_zero_of_not_mem

theorem cosineSeries_term_eq_zero (x : ℝ) (n : ℤ) (hn : n ∉ ({1, -1} : Finset ℤ)) :
    fourier n (x : AddCircle (1 : ℝ)) * cosineCoeff n = 0 := by
  rw [cosineCoeff_eq_zero_of_not_mem n hn, mul_zero]

/-- The profile Fourier series of `cosineCoeff` is the cosine. -/
theorem cosineCoeff_series (x : ℝ) :
    profileFourierSeries cosineCoeff x = ((Real.cos (2 * Real.pi * x) : ℝ) : ℂ) := by
  unfold profileFourierSeries
  rw [tsum_eq_sum (cosineSeries_term_eq_zero x),
    Finset.sum_pair (by norm_num : (1 : ℤ) ≠ -1), cosineCoeff_one, cosineCoeff_neg_one,
    fourier_coe_apply, fourier_coe_apply, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- Real scalars pass through the profile Fourier synthesis. -/
theorem profileFourierSeries_real_smul (c : ℤ → ℂ) (M x : ℝ) :
    profileFourierSeries (fun n => M • c n) x = M • profileFourierSeries c x := by
  unfold profileFourierSeries
  simp only [mul_smul_comm]
  exact tsum_const_smul'' M

/-! ### The zero-start memory of the unit mode -/

/-- `m(t) = ∫_a^t e^{-4π²(t-s)} r(s) ds`, the zero-start memory of the unit transverse mode. -/
def cosineMemory (r : ℝ → ℝ) (a t : ℝ) : ℝ :=
  ∫ s in a..t, Real.exp (-(4 * Real.pi ^ 2) * (t - s)) * r s

/-- With metric weight one, the transverse propagator is the plain exponential. -/
theorem transverseModeKernel_unit (g : ℝ → ℝ) (hg : ∀ s, g s = 1) (rate s t : ℝ) :
    transverseModeKernel rate g s t = Real.exp (-rate * (t - s)) := by
  have hg' : g = fun _ => (1 : ℝ) := funext hg
  subst hg'
  unfold transverseModeKernel
  simp

/-- The Fourier modes of the response to a cosine source. -/
theorem profileModeResponse_cosine (g : ℝ → ℝ) (hg : ∀ s, g s = 1) (r : ℝ → ℝ)
    (f : ℝ → ℝ → ℂ) (hf : ∀ s x, f s x = ((r s * Real.cos (2 * Real.pi * x) : ℝ) : ℂ))
    (a t : ℝ) (n : ℤ) :
    profileModeResponse g f a t n = cosineMemory r a t • cosineCoeff n := by
  have hcoef : ∀ s, unitProfileFourierCoeff (f s) n = r s • cosineCoeff n := by
    intro s
    have hfs : f s = fun x => r s • profileFourierSeries cosineCoeff x := by
      funext x
      rw [hf s x, cosineCoeff_series, Complex.real_smul, Complex.ofReal_mul]
    rw [hfs, unitProfileFourierCoeff_real_smul (profileFourierSeries cosineCoeff) (r s) n,
      unitProfileFourierCoeff_profileFourierSeries cosineCoeff summable_cosineCoeff n]
  unfold profileModeResponse transverseModeResponse cosineMemory
  simp only [hcoef, smul_smul]
  by_cases hn : n = 1 ∨ n = -1
  · have hrate : ‖profileFourierFrequency n‖ ^ 2 = 4 * Real.pi ^ 2 := by
      rw [profileFourierFrequency_norm_sq]
      rcases hn with rfl | rfl <;> norm_num
    have hk : ∀ s, transverseModeKernel (‖profileFourierFrequency n‖ ^ 2) g s t =
        Real.exp (-(4 * Real.pi ^ 2) * (t - s)) := by
      intro s
      rw [hrate]
      exact transverseModeKernel_unit g hg _ s t
    simp only [hk]
    rw [intervalIntegral.integral_smul_const]
  · rw [cosineCoeff_of_not n hn]
    simp

/-- **The flat response to a cosine source.** With metric weight one, the finite-past
transverse response to `r(s) cos(2πx)` is `m(t) cos(2πx)`. -/
theorem profileCellResponse_cosine (g : ℝ → ℝ) (hg : ∀ s, g s = 1) (r : ℝ → ℝ)
    (f : ℝ → ℝ → ℂ) (hf : ∀ s x, f s x = ((r s * Real.cos (2 * Real.pi * x) : ℝ) : ℂ))
    (a t x : ℝ) :
    profileCellResponse g f a t x =
      ((cosineMemory r a t * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) := by
  unfold profileCellResponse
  rw [show profileModeResponse g f a t = fun n => cosineMemory r a t • cosineCoeff n from
      funext (profileModeResponse_cosine g hg r f hf a t),
    profileFourierSeries_real_smul cosineCoeff (cosineMemory r a t) x, cosineCoeff_series,
    Complex.ofReal_mul (cosineMemory r a t) (Real.cos (2 * Real.pi * x)), Complex.real_smul]

/-! ### The cosine shear profile -/

/-- The unit-frequency shear profile `A(t) cos(2πx)`. -/
def cosineShear (A : ℝ → ℝ) (t x : ℝ) : ℝ := A t * Real.cos (2 * Real.pi * x)

theorem cosineShear_contDiff (A : ℝ → ℝ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cosineShear A t) := by
  unfold cosineShear
  fun_prop

theorem cosineShear_periodic (A : ℝ → ℝ) (t : ℝ) : Function.Periodic (cosineShear A t) 1 := by
  intro x
  unfold cosineShear
  have he : 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi := by ring
  rw [he, Real.cos_add_two_pi]

theorem cosineShear_mean_zero (A : ℝ → ℝ) (t : ℝ) :
    (∫ s in (0 : ℝ)..1, cosineShear A t s) = 0 := by
  unfold cosineShear
  rw [intervalIntegral.integral_const_mul, EntryWeakProofs.unitCosine_interval_mean, mul_zero]

end AVRegularity.CycleComparison.Diagonal
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Diagonal

/-! The order-two diagonal letter for the flat metric and a cosine shear (on pulse `j` the flat
zero-past solution is `χ_{I,j} = -(√η/e) M_j 𝐮_j`, and `⟨𝐮_j ⊗ 𝐮_j⟩ = μ H_* Π_j`). The order-two
letter is `⟨w_l χ_{α'}⟩ - η G_{l α'}`. For `G = I` and the drift `v = A(t) cos(2π z_⊥) e_∥`, the
first lift is `χ = -√η m(t) cos(2π z_⊥) e_∥ ⊗ ∇_X`, `m(t) = ∫_{t₀}^t e^{-4π²(t-s)} A(s) ds`
(`flat_first_coefficient`), and the letter is the scalar `flatCosineLetter` times the identity:
`(η/2)(-A m)` on `e_∥ ⊗ e_∥` minus `η I`. -/

section
open AVRegularity.CycleComparison.Lift AVRegularity.CycleComparison.LiftMeanEntrywise

/-- The zero-start memory only sees the source on `[a, t]`. -/
theorem cosineMemory_congr (r r' : ℝ → ℝ) (a t : ℝ) (hat : a ≤ t)
    (hr : ∀ s ∈ Set.Icc a t, r s = r' s) : cosineMemory r a t = cosineMemory r' a t := by
  unfold cosineMemory
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hat] at hs
  simp only [hr s hs]

/-- The scalar of the flat order-two letter for the cosine shear `A(t) cos(2π z_⊥) e_∥`:
`(1/2) √η A(t) m(t) (e_∥)_l (e_∥)_{α'} - η δ_{l α'}`, with
`m(t) = -√η ∫_a^t e^{-4π²(t-s)} A(s) ds`. -/
def flatCosineLetter (η : ℝ) (par : Fin 2) (A : ℝ → ℝ) (a t : ℝ) (α : DerivativeWord2 1)
    (l : Fin 2) : ℝ :=
  1 / 2 * (Real.sqrt η * A t * cosineMemory (fun s => -(Real.sqrt η * A s)) a t) *
      (basisVec par l * basisVec par (α 0)) + -η * (if l = α 0 then 1 else 0)

section Setting
variable {ι : Type*} [hfin : Fintype ι] [hdec : DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [hfd : ∀ i, FiniteDimensional ℝ (h i)] [hcs : ∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {bm : ι → ι → ℝ} {Θ : ℝ}
include hfin hdec hfd hcs

omit hfin hfd hcs in
/-- The order-two letter at tested order two is the order-two diagonal mean flux coefficient. -/
theorem diagonalMeanLetter_two_eq (Cc : ℕ → ℕ → LiftCoeff ι h) (α : DerivativeWord2 1)
    (t : ℝ) (X : Vec 2) (l : Fin 2) (v u : ι) :
    diagonalMeanLetter Q Cc 2 2 α t X l v u =
      diagonalMeanFluxCoefficient Q Cc 2 l 1 α t X 0 v u :=
  truncatedMeanCoefficient_eq 2 2 le_rfl le_rfl _ α t X l v u

omit hfin hfd hcs in
/-- The order-two letter: `⟨w_l C_1⟩ - η G_{l α'}`. -/
theorem diagonalMeanLetter_two_apply (Cc : ℕ → ℕ → LiftCoeff ι h) (α : DerivativeWord2 1)
    (t : ℝ) (X : Vec 2) (l : Fin 2) (v u : ι) :
    diagonalMeanLetter Q Cc 2 2 α t X l v u =
      fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z l) • Cc 0 1 1 α t X z v u) +
        (-Q.η * Q.G t X l (α 0)) • blockIdentityEntry h v u := by
  rw [diagonalMeanLetter_two_eq]
  show weightedLiftCoefficientMean (Cc 0 (2 - 1)) (fun s y => Real.sqrt Q.η * Q.v s y l) 1 α t X
      0 v u + (if (2 : ℕ) = 2 then metricFluxCoefficient (h := h) Q.η Q.G l 1 α t X 0 v u
        else 0) = _
  rw [ite_eq_left (rfl : (2 : ℕ) = 2), metricFluxCoefficient_one]
  rfl

omit hdec in
/-- The first flat lift for a cosine shear. -/
theorem flat_first_coefficient
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bm Θ)
    (hG : ∀ t X i j, Q.G t X i j = if i = j then 1 else 0)
    (A : ℝ → ℝ) (hV : ∀ t x, V t x = A t * Real.cos (2 * Real.pi * x))
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (α : DerivativeWord2 1) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    Cc 0 1 1 α t X z v v =
      ((cosineMemory (fun s => -(Real.sqrt Q.η * A s)) a t *
          Real.cos (2 * Real.pi * z par.rev)) * basisVec par (α 0)) •
        ContinuousLinearMap.id ℝ (h v) := by
  have hf : ∀ s x, clampedFirstSourceProfile Q.η V a b P.window 1 s x =
      ((-(Real.sqrt Q.η * A (Set.projIcc a b P.window s)) * Real.cos (2 * Real.pi * x) : ℝ) :
        ℂ) := by
    intro s x
    unfold clampedFirstSourceProfile
    rw [hV]
    congr 1
    ring
  have hresp := profileCellResponse_cosine
    (fun r => Q.G (Set.projIcc a b P.window r) X par.rev par.rev)
    (fun _ => (hG _ X _ _).trans (ite_eq_left rfl))
    (fun s => -(Real.sqrt Q.η * A (Set.projIcc a b P.window s)))
    (clampedFirstSourceProfile Q.η V a b P.window 1) hf a t (z par.rev)
  have hmem : cosineMemory (fun s => -(Real.sqrt Q.η * A (Set.projIcc a b P.window s))) a t =
      cosineMemory (fun s => -(Real.sqrt Q.η * A s)) a t :=
    cosineMemory_congr _ _ a t ht.1 (fun s hs => by
      simp only [Set.projIcc_of_mem P.window ⟨hs.1, hs.2.trans ht.2⟩])
  rw [liftCoefficient_first_diagonal_scalar P sX sZ Cc hseq α t ht X z v, hresp,
    Complex.ofReal_re, hmem]

omit hdec in
/-- The drift average of the flat first lift. -/
theorem flat_weighted_mean
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bm Θ)
    (hG : ∀ t X i j, Q.G t X i j = if i = j then 1 else 0)
    (A : ℝ → ℝ) (hV : ∀ t x, V t x = A t * Real.cos (2 * Real.pi * x))
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (α : DerivativeWord2 1) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) (l : Fin 2) (v : ι) :
    fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z l) • Cc 0 1 1 α t X z v v) =
      (1 / 2 * (Real.sqrt Q.η * A t * cosineMemory (fun s => -(Real.sqrt Q.η * A s)) a t) *
        (basisVec par l * basisVec par (α 0))) • ContinuousLinearMap.id ℝ (h v) := by
  have hvl : ∀ z : Vec 2,
      Q.v t z l = A t * Real.cos (2 * Real.pi * z par.rev) * basisVec par l := by
    intro z
    rw [P.v_shear t z, Pi.smul_apply, smul_eq_mul, hV]
  have hpt : ∀ z : Vec 2, (Real.sqrt Q.η * Q.v t z l) • Cc 0 1 1 α t X z v v =
      (Real.sqrt Q.η * A t * cosineMemory (fun s => -(Real.sqrt Q.η * A s)) a t *
        (basisVec par l * basisVec par (α 0)) * Real.cos (2 * Real.pi * z par.rev) ^ 2) •
          ContinuousLinearMap.id ℝ (h v) := by
    intro z
    rw [flat_first_coefficient P hG A hV sX sZ Cc hseq α t ht X z v, smul_smul, hvl z]
    congr 1
    ring
  have hc2 : ∫ z in AVenhance.unitCube, Real.cos (2 * Real.pi * z par.rev) ^ 2 = 1 / 2 := by
    simpa only [add_zero] using AVRegularity.CycleDamping.cell_cosine_sq_mean par.rev 0
  unfold fieldCellMean
  simp_rw [hpt]
  rw [integral_smul_const, MeasureTheory.integral_const_mul, hc2]
  congr 1
  ring

/-- **The flat order-two letter.** For the flat metric and a cosine shear, the order-two
diagonal letter on a diagonal block is `flatCosineLetter` times the identity. -/
theorem flat_diagonalMeanLetter_two
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bm Θ)
    (hG : ∀ t X i j, Q.G t X i j = if i = j then 1 else 0)
    (A : ℝ → ℝ) (hV : ∀ t x, V t x = A t * Real.cos (2 * Real.pi * x))
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (α : DerivativeWord2 1) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) (l : Fin 2) (v : ι) :
    diagonalMeanLetter Q Cc 2 2 α t X l v v =
      flatCosineLetter Q.η par A a t α l • ContinuousLinearMap.id ℝ (h v) := by
  rw [diagonalMeanLetter_two_apply, flat_weighted_mean P hG A hV sX sZ Cc hseq α t ht X l v, hG,
    blockIdentityEntry_self]
  unfold flatCosineLetter
  rw [add_smul]

end Setting
end

/-! The flat order-two letter of a pulse against the reference flux (`M_j' + μ M_j = p_j`,
`⟨𝐮_j ⊗ 𝐮_j⟩ = μ H_* Π_j` and `B η ℓ² = e²` give `B 𝖣_{I,j} = ν I + μ H_* p_j M_j Π_j`; an
all-time corrector adds the explicit switching price).

For the pulse `k` the drift of the lift is the cosine shear of amplitude
`A(𝗍) = ±(e^{1+α}/ν) 2π p_k(ℓ²𝗍)` (`pulseShearAmplitude`). Its zero-start flat memory is
`ℓ⁻² ∫_{ℓ²t₀}^{ℓ²t} e^{-μ(ℓ²t - r)} p_k(r) dr` (`cosineMemory_scaled`, `μℓ² = 4π²`), and the
reference memory differs from it by the switching term
`M_k(ℓ²t) - M̃(ℓ²t) = e^{-μ(ℓ²t - ℓ²t₀)} M_k(ℓ²t₀)` (`ocPulseMemory_sub_interval`). On the lift
window only the pulse `k` is active, so `J = ν I + μ H_* p_k M_k Π_k` there
(`ocRefFlux_window_entry`). Hence `B · (flat letter) + J = μ H_* p_k e^{-μ(…)} M_k(ℓ²t₀) Π_k`
exactly (`pulse_flat_add_refFlux`), of size at most `μ H_* M_k(ℓ²t₀)`. -/

/-! ### Real scalings -/

/-- `x^{2y} = (x^y)²` for `x ≥ 0`. -/
theorem rpow_two_mul_eq_sq' {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (2 * y) = (x ^ y) ^ 2 := by
  rw [mul_comm, Real.rpow_mul hx, Real.rpow_two]

/-- `ℓ² = e²/ν`. -/
theorem ocEll_sq_eq_div {q : ℝ} {Λ m : ℕ} {ν : ℝ} (hν : 0 < ν) :
    ocEll q Λ m ν ^ 2 = ocEpsilon q Λ m ^ 2 / ν := by
  rw [ocEll, div_pow, Real.sq_sqrt hν.le]

/-- `μ ℓ² = 4π²`. -/
theorem ocMu_mul_ocEll_sq_eq {q : ℝ} {Λ m : ℕ} {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) :
    ocMu q Λ m ν * ocEll q Λ m ν ^ 2 = 4 * Real.pi ^ 2 := by
  have he : 0 < ocEpsilon q Λ m := AVRegularity.Construction.Stream.ocEpsilon_pos hΛ
  rw [ocEll_sq_eq_div hν, ocMu]
  field_simp

/-- `μ H_* · 2ℓ² = ν (e^{1+α}/ν)² 4π²`. -/
theorem ocMu_mul_ocHStar_mul_ocEll_sq {α q : ℝ} {Λ m : ℕ} {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) :
    ocMu q Λ m ν * ocHStar α q Λ m ν * (2 * ocEll q Λ m ν ^ 2) =
      ν * (ocEpsilon q Λ m ^ (1 + α) / ν) ^ 2 * (4 * Real.pi ^ 2) := by
  have he : 0 < ocEpsilon q Λ m := AVRegularity.Construction.Stream.ocEpsilon_pos hΛ
  rw [ocEll_sq_eq_div hν, ocMu, ocHStar, rpow_two_mul_eq_sq' he.le]
  field

/-! ### The zero-start memory of a pulse -/

/-- The unit-mode memory of a time-rescaled source is the physical memory, rescaled. -/
theorem cosineMemory_scaled (p : ℝ → ℝ) (c ℓsq μ a t : ℝ) (hℓ : 0 < ℓsq)
    (hμ : μ * ℓsq = 4 * Real.pi ^ 2) :
    cosineMemory (fun s => c * p (ℓsq * s)) a t =
      c * (ℓsq⁻¹ * ∫ r in (ℓsq * a)..(ℓsq * t), Real.exp (-μ * (ℓsq * t - r)) * p r) := by
  have hcv := intervalIntegral.integral_comp_mul_left (a := a) (b := t)
    (fun r => Real.exp (-μ * (ℓsq * t - r)) * (c * p r)) hℓ.ne'
  have hpt : ∀ s, Real.exp (-(4 * Real.pi ^ 2) * (t - s)) * (c * p (ℓsq * s)) =
      Real.exp (-μ * (ℓsq * t - ℓsq * s)) * (c * p (ℓsq * s)) := by
    intro s
    have he : -(4 * Real.pi ^ 2) * (t - s) = -μ * (ℓsq * t - ℓsq * s) := by
      rw [← hμ]
      ring
    rw [he]
  have hpt2 : ∀ r, Real.exp (-μ * (ℓsq * t - r)) * (c * p r) =
      c * (Real.exp (-μ * (ℓsq * t - r)) * p r) := fun r => by ring
  unfold cosineMemory
  simp_rw [hpt]
  rw [hcv]
  simp_rw [hpt2]
  rw [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

/-- The causal memory splits at an earlier time `T₀` into the decayed memory at `T₀` and the
zero-start memory on `[T₀, T]`. -/
theorem weightedMemory_split (p : ℝ → ℝ) (hp : Continuous p) (hc : HasCompactSupport p)
    (μ T₀ T : ℝ) :
    (∫ s in Set.Iic T, p s * Real.exp (μ * (s - T))) -
        ∫ r in T₀..T, Real.exp (-μ * (T - r)) * p r =
      Real.exp (-μ * (T - T₀)) * ∫ s in Set.Iic T₀, p s * Real.exp (μ * (s - T₀)) := by
  have hcont : Continuous (fun s => p s * Real.exp (μ * (s - T))) := by fun_prop
  have hfi : Integrable (fun s => p s * Real.exp (μ * (s - T))) :=
    hcont.integrable_of_hasCompactSupport hc.mul_right
  have hsplit := intervalIntegral.integral_Iic_sub_Iic (μ := volume)
    (f := fun s => p s * Real.exp (μ * (s - T))) (a := T₀) (b := T)
    hfi.integrableOn hfi.integrableOn
  have hk : (fun r => Real.exp (-μ * (T - r)) * p r) =
      fun x => p x * Real.exp (μ * (x - T)) := by
    funext x
    rw [mul_comm (Real.exp (-μ * (T - x))) (p x), show -μ * (T - x) = μ * (x - T) by ring]
  have hfun : (fun s => p s * Real.exp (μ * (s - T))) =
      fun s => Real.exp (-μ * (T - T₀)) * (p s * Real.exp (μ * (s - T₀))) := by
    funext s
    rw [show μ * (s - T) = -μ * (T - T₀) + μ * (s - T₀) by ring, Real.exp_add]
    ring
  rw [hk, ← hsplit, hfun]
  simp only [MeasureTheory.integral_const_mul]
  ring

/-- `M_k(T) - ∫_{T₀}^T e^{-μ(T-r)} p_k(r) dr = e^{-μ(T-T₀)} M_k(T₀)`. -/
theorem ocPulseMemory_sub_interval {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) (ν : ℝ) (k : ℤ) (T₀ T : ℝ) :
    ocPulseMemory α q Λ ζ m ν k T -
        ∫ r in T₀..T, Real.exp (-(ocMu q Λ m ν) * (T - r)) * ocPulse α q Λ ζ m k r =
      Real.exp (-(ocMu q Λ m ν) * (T - T₀)) * ocPulseMemory α q Λ ζ m ν k T₀ := by
  rw [CycleReference.ocPulseMemory_eq_weighted_Iic, CycleReference.ocPulseMemory_eq_weighted_Iic]
  exact weightedMemory_split _ (CycleReference.ocPulse_continuous hζ k)
    (CycleReference.ocPulse_hasCompactSupport hΛ hζ k) _ T₀ T

/-! ### The reference flux on the lift window -/

/-- On the lift window of the pulse `k`, every other odd pulse vanishes. -/
theorem ocPulse_eq_zero_of_mem_window {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) {kp j : ℤ} (hk : Odd kp) (hj : Odd j) (hne : j ≠ kp) {T : ℝ}
    (hT : T ∈ ocPulseWindow α q Λ m kp) : ocPulse α q Λ ζ m j T = 0 := by
  by_contra hp
  have hd := CycleReference.pulse_nonzero_center_distance hΛ hζ hp
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hT' : ((kp : ℝ) - 61 / 48) * ocTau α q Λ m ≤ T ∧
      T ≤ ((kp : ℝ) + 61 / 48) * ocTau α q Λ m := hT
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hgap : j + 2 ≤ kp := by
      obtain ⟨a, ha⟩ := hk
      obtain ⟨c, hc⟩ := hj
      omega
    have hgapR : (j : ℝ) + 2 ≤ (kp : ℝ) := by exact_mod_cast hgap
    have hmul := mul_le_mul_of_nonneg_right hgapR hτ.le
    linarith [hd.2, hT'.1]
  · have hgap : kp + 2 ≤ j := by
      obtain ⟨a, ha⟩ := hk
      obtain ⟨c, hc⟩ := hj
      omega
    have hgapR : (kp : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hgap
    have hmul := mul_le_mul_of_nonneg_right hgapR hτ.le
    linarith [hd.1, hT'.2]

/-- `Π_k = e_∥ ⊗ e_∥` with `e_∥ = basisVec (pulseParallel k)`. -/
theorem ocPi_eq_basisVec_mul {kp : ℤ} (hk : Odd kp) (i j : Fin 2) :
    ocPi ⟨kp, hk⟩ i j = basisVec (EntryWeakProofs.pulseParallel kp) i *
      basisVec (EntryWeakProofs.pulseParallel kp) j := by
  by_cases h1 : kp % 4 = 1 <;> fin_cases i <;> fin_cases j <;>
    simp [ocPi, EntryWeakProofs.pulseParallel, h1]

/-- **The reference flux on the lift window.** -/
theorem ocRefFlux_window_entry {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) (ν : ℝ) {kp : ℤ} (hk : Odd kp) {T : ℝ}
    (hT : T ∈ ocPulseWindow α q Λ m kp) (i j : Fin 2) :
    ocRefFlux α q Λ ζ m ν T i j = ν * (if i = j then 1 else 0) +
      ocMu q Λ m ν * ocHStar α q Λ m ν *
        (ocPulse α q Λ ζ m kp T * ocPulseMemory α q Λ ζ m ν kp T) *
          (basisVec (EntryWeakProofs.pulseParallel kp) i *
            basisVec (EntryWeakProofs.pulseParallel kp) j) := by
  have hsum : (∑' k : {k : ℤ // Odd k},
      (ocPulse α q Λ ζ m k.1 T * ocPulseMemory α q Λ ζ m ν k.1 T) • ocPi k) =
      (ocPulse α q Λ ζ m kp T * ocPulseMemory α q Λ ζ m ν kp T) • ocPi ⟨kp, hk⟩ := by
    by_cases hp : ocPulse α q Λ ζ m kp T = 0
    · have hall : ∀ k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 T = 0 := by
        intro k
        by_cases hkk : k.1 = kp
        · rw [hkk]
          exact hp
        · exact ocPulse_eq_zero_of_mem_window hΛ hζ hk k.2 hkk hT
      rw [CycleReference.pulseMatrixSum_eq_zero_of_quiet ν T hall, hp, zero_mul, zero_smul]
    · exact CycleReference.pulseMatrixSum_eq_at_active hΛ hζ ν T ⟨kp, hk⟩ hp
  have hmat : ocRefFlux α q Λ ζ m ν T = ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      (ocMu q Λ m ν * ocHStar α q Λ m ν *
        (ocPulse α q Λ ζ m kp T * ocPulseMemory α q Λ ζ m ν kp T)) • ocPi ⟨kp, hk⟩ := by
    rw [ocRefFlux, hsum, smul_smul]
  rw [hmat, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, smul_eq_mul, ocPi_eq_basisVec_mul hk]

/-! ### The flat letter of a pulse against the reference flux -/

/-- The scalar algebra of `B 𝖣_{I} + J`. -/
theorem flat_flux_scalar (B η ν s σ c p Mt M ℓ μ H δ bb : ℝ) (hBη : B * η = ν)
    (hs : s * s = η) (hσ : σ * σ = 1) (hℓ : ℓ * ℓ⁻¹ = 1)
    (hμH : μ * H * (2 * ℓ) = ν * c ^ 2 * (4 * Real.pi ^ 2)) :
    B * (1 / 2 * (s * (σ * c * (2 * Real.pi * p)) *
        (-(s * (σ * c * (2 * Real.pi))) * (ℓ⁻¹ * Mt))) * bb + -η * δ) +
      (ν * δ + μ * H * (p * M) * bb) =
    μ * H * p * (M - Mt) * bb := by
  linear_combination
    (-(1 / 2) * B * σ ^ 2 * (c ^ 2 * (4 * Real.pi ^ 2) * ℓ⁻¹) * (p * Mt * bb)) * hs +
    (-(1 / 2) * B * η * (c ^ 2 * (4 * Real.pi ^ 2) * ℓ⁻¹) * (p * Mt * bb)) * hσ +
    (-(1 / 2) * (c ^ 2 * (4 * Real.pi ^ 2) * ℓ⁻¹) * (p * Mt * bb) - δ) * hBη +
    (1 / 2 * ℓ⁻¹ * (p * Mt * bb)) * hμH +
    (-(μ * H * (p * Mt * bb))) * hℓ

/-- **The flat letter against the reference flux.** On the lift window of the pulse `k`, the
flat order-two letter, scaled by `B`, plus the reference flux, is exactly the switching term. -/
theorem pulse_flat_add_refFlux {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) {kp : ℤ} (hk : Odd kp)
    (t₀ t : ℝ) (hT : ocEll q Λ m ν ^ 2 * t ∈ ocPulseWindow α q Λ m kp)
    (α' : DerivativeWord2 1) (l : Fin 2) :
    B * flatCosineLetter (ν / B) (EntryWeakProofs.pulseParallel kp)
        (EntryWeakProofs.pulseShearAmplitude α q Λ m ζ ν kp) t₀ t α' l +
      ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) l (α' 0) =
    ocMu q Λ m ν * ocHStar α q Λ m ν * ocPulse α q Λ ζ m kp (ocEll q Λ m ν ^ 2 * t) *
      (Real.exp (-(ocMu q Λ m ν) * (ocEll q Λ m ν ^ 2 * t - ocEll q Λ m ν ^ 2 * t₀)) *
        ocPulseMemory α q Λ ζ m ν kp (ocEll q Λ m ν ^ 2 * t₀)) *
      (basisVec (EntryWeakProofs.pulseParallel kp) l *
        basisVec (EntryWeakProofs.pulseParallel kp) (α' 0)) := by
  have he : 0 < ocEpsilon q Λ m := AVRegularity.Construction.Stream.ocEpsilon_pos hΛ
  have hℓpos : 0 < ocEll q Λ m ν ^ 2 := by
    rw [ocEll_sq_eq_div hν]
    exact div_pos (pow_pos he 2) hν
  have hμℓ : ocMu q Λ m ν * ocEll q Λ m ν ^ 2 = 4 * Real.pi ^ 2 :=
    ocMu_mul_ocEll_sq_eq hΛ hν
  have hfunA : (fun s => -(Real.sqrt (ν / B) *
      EntryWeakProofs.pulseShearAmplitude α q Λ m ζ ν kp s)) =
      fun s => -(Real.sqrt (ν / B) * ((if kp % 4 = 1 then (1 : ℝ) else -1) *
        (ocEpsilon q Λ m ^ (1 + α) / ν) * (2 * Real.pi))) *
          ocPulse α q Λ ζ m kp (ocEll q Λ m ν ^ 2 * s) := by
    funext s
    unfold EntryWeakProofs.pulseShearAmplitude
    ring
  have hcm : cosineMemory (fun s => -(Real.sqrt (ν / B) *
      EntryWeakProofs.pulseShearAmplitude α q Λ m ζ ν kp s)) t₀ t =
      -(Real.sqrt (ν / B) * ((if kp % 4 = 1 then (1 : ℝ) else -1) *
        (ocEpsilon q Λ m ^ (1 + α) / ν) * (2 * Real.pi))) *
      ((ocEll q Λ m ν ^ 2)⁻¹ *
        ∫ r in (ocEll q Λ m ν ^ 2 * t₀)..(ocEll q Λ m ν ^ 2 * t),
          Real.exp (-(ocMu q Λ m ν) * (ocEll q Λ m ν ^ 2 * t - r)) *
            ocPulse α q Λ ζ m kp r) := by
    rw [hfunA, cosineMemory_scaled (ocPulse α q Λ ζ m kp)
      (-(Real.sqrt (ν / B) * ((if kp % 4 = 1 then (1 : ℝ) else -1) *
        (ocEpsilon q Λ m ^ (1 + α) / ν) * (2 * Real.pi)))) _ _ t₀ t hℓpos hμℓ]
  have hAt : EntryWeakProofs.pulseShearAmplitude α q Λ m ζ ν kp t =
      (if kp % 4 = 1 then (1 : ℝ) else -1) * (ocEpsilon q Λ m ^ (1 + α) / ν) *
        (2 * Real.pi * ocPulse α q Λ ζ m kp (ocEll q Λ m ν ^ 2 * t)) := rfl
  have hJ := ocRefFlux_window_entry (ζ := ζ) hΛ hζ ν hk hT l (α' 0)
  have hsub := ocPulseMemory_sub_interval (α := α) (q := q) (m := m) hΛ hζ ν kp
    (ocEll q Λ m ν ^ 2 * t₀) (ocEll q Λ m ν ^ 2 * t)
  have hBη : B * (ν / B) = ν := mul_div_cancel₀ ν hB.ne'
  have hs : Real.sqrt (ν / B) * Real.sqrt (ν / B) = ν / B :=
    Real.mul_self_sqrt (div_nonneg hν.le hB.le)
  have hσ : (if kp % 4 = 1 then (1 : ℝ) else -1) * (if kp % 4 = 1 then (1 : ℝ) else -1) = 1 := by
    split_ifs <;> norm_num
  have hℓinv : ocEll q Λ m ν ^ 2 * (ocEll q Λ m ν ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hℓpos.ne'
  have key := flat_flux_scalar _ _ _ _ _ _ (ocPulse α q Λ ζ m kp (ocEll q Λ m ν ^ 2 * t))
    (∫ r in (ocEll q Λ m ν ^ 2 * t₀)..(ocEll q Λ m ν ^ 2 * t),
      Real.exp (-(ocMu q Λ m ν) * (ocEll q Λ m ν ^ 2 * t - r)) * ocPulse α q Λ ζ m kp r)
    (ocPulseMemory α q Λ ζ m ν kp (ocEll q Λ m ν ^ 2 * t)) _ _ _
    (if l = α' 0 then (1 : ℝ) else 0)
    (basisVec (EntryWeakProofs.pulseParallel kp) l *
      basisVec (EntryWeakProofs.pulseParallel kp) (α' 0))
    hBη hs hσ hℓinv (ocMu_mul_ocHStar_mul_ocEll_sq (α := α) (q := q) (m := m) hΛ hν)
  unfold flatCosineLetter
  rw [hcm, hAt, hJ]
  linear_combination key + (ocMu q Λ m ν * ocHStar α q Λ m ν *
    ocPulse α q Λ ζ m kp (ocEll q Λ m ν ^ 2 * t) *
      (basisVec (EntryWeakProofs.pulseParallel kp) l *
        basisVec (EntryWeakProofs.pulseParallel kp) (α' 0))) * hsub

/-- A product of two basis coordinates has size at most one. -/
theorem abs_basisVec_mul_le (P i j : Fin 2) : |basisVec P i * basisVec P j| ≤ 1 := by
  simp only [basisVec_apply]
  split_ifs <;> norm_num

/-- The size of the switching term. -/
theorem switching_term_abs_le (μ H p E M₀ bb : ℝ) (hμH : 0 ≤ μ * H) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hM : 0 ≤ M₀) (hbb : |bb| ≤ 1) :
    |μ * H * p * (E * M₀) * bb| ≤ μ * H * M₀ := by
  have hX : 0 ≤ μ * H * p * (E * M₀) := mul_nonneg (mul_nonneg hμH hp0) (mul_nonneg hE0 hM)
  have hpE : p * E ≤ 1 := by
    have h11 := mul_le_mul hp1 hE1 hE0 zero_le_one
    linarith
  rw [abs_mul, abs_of_nonneg hX]
  calc μ * H * p * (E * M₀) * |bb| ≤ μ * H * p * (E * M₀) * 1 :=
        mul_le_mul_of_nonneg_left hbb hX
    _ = μ * H * (p * E) * M₀ := by ring
    _ ≤ μ * H * 1 * M₀ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpE hμH) hM
    _ = μ * H * M₀ := by ring

/-- **The switching bound.** On the lift window of the pulse `k`, for `t₀ ≤ t`,
`|B · (flat letter) + J| ≤ μ H_* M_k(ℓ²t₀)`. -/
theorem pulse_flat_add_refFlux_abs_le {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B) {kp : ℤ} (hk : Odd kp)
    {t₀ t : ℝ} (ht : t₀ ≤ t) (hT : ocEll q Λ m ν ^ 2 * t ∈ ocPulseWindow α q Λ m kp)
    (α' : DerivativeWord2 1) (l : Fin 2) :
    |B * flatCosineLetter (ν / B) (EntryWeakProofs.pulseParallel kp)
        (EntryWeakProofs.pulseShearAmplitude α q Λ m ζ ν kp) t₀ t α' l +
      ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) l (α' 0)| ≤
    ocMu q Λ m ν * ocHStar α q Λ m ν * ocPulseMemory α q Λ ζ m ν kp (ocEll q Λ m ν ^ 2 * t₀) := by
  rw [pulse_flat_add_refFlux hΛ hζ hν hB hk t₀ t hT α' l]
  have he : 0 < ocEpsilon q Λ m := AVRegularity.Construction.Stream.ocEpsilon_pos hΛ
  have hℓpos : 0 < ocEll q Λ m ν ^ 2 := by
    rw [ocEll_sq_eq_div hν]
    exact div_pos (pow_pos he 2) hν
  have hμ : 0 < ocMu q Λ m ν := CycleReference.ocMu_pos hΛ hν
  have hH : 0 < ocHStar α q Λ m ν := CycleReference.ocHStar_pos hΛ hν
  have hp := CycleReference.ocPulse_range (α := α) (q := q) (Λ := Λ) (m := m) hζ kp
    (ocEll q Λ m ν ^ 2 * t)
  have hM := (CycleReference.ocPulseMemory_range (α := α) (q := q) (m := m) hΛ hζ ν hν kp
    (ocEll q Λ m ν ^ 2 * t₀)).1
  have hE1 : Real.exp (-(ocMu q Λ m ν) * (ocEll q Λ m ν ^ 2 * t - ocEll q Λ m ν ^ 2 * t₀)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h1 : 0 ≤ ocMu q Λ m ν * (ocEll q Λ m ν ^ 2 * (t - t₀)) :=
      mul_nonneg hμ.le (mul_nonneg hℓpos.le (sub_nonneg.mpr ht))
    linarith
  exact switching_term_abs_le _ _ _ _ _ _ (mul_nonneg hμ.le hH.le) hp.1 hp.2
    (Real.exp_pos _).le hE1 hM (abs_basisVec_mul_le _ _ _)

end AVRegularity.CycleComparison.Diagonal
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Diagonal

/-! Identical-history metric stability of the order-two diagonal letter (at `H = 0`, changing `G`
to `I` with identical drift and history changes scalar energy and mean coefficients by `Cg`; for
the scaled letter the cost is `C B g_m`).

For lift data `Q` of any depth whose drift is a cosine shear `A(t) cos(2π z_⊥) e_∥`, the
order-two letter differs from the flat letter `flatCosineLetter` by `C g λ^r` in its slow jets:
the grade-zero lifts do not see the edges (`isLiftSetting_zeroEdge`), the paired-flux bound of the
lift library compares the edge-free data with its identity-metric version, and the identity-metric
letter is computed exactly (`flat_diagonalMeanLetter_two`). The last statement adds a constant
multiple of the identity, whose only jet is the value. -/

open AVRegularity.CycleComparison.Lift AVRegularity.CycleComparison.LiftMeanEntrywise

/-- The jets of `B • L + J • T` against those of `L - S • T`: only the value sees the constant
`(B S + J) T`. -/
theorem norm_iteratedFDeriv_smul_add_const_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (j : ℕ) (L : Vec 2 → F) (T : F) (B S J : ℝ) (hB : 0 ≤ B)
    (hL : ContDiff ℝ (j : ℕ∞) L) (X : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun Y => B • L Y + J • T) X‖ ≤
      B * ‖iteratedFDeriv ℝ j (fun Y => L Y - S • T) X‖ +
        (if j = 0 then |B * S + J| * ‖T‖ else 0) := by
  have hfun : (fun Y => B • L Y + J • T) = fun Y => B • (L Y - S • T) + (B * S + J) • T := by
    funext Y
    rw [smul_sub, smul_smul, add_smul]
    abel
  have hg : ContDiff ℝ (j : ℕ∞) (fun Y => L Y - S • T) := hL.sub contDiff_const
  rw [hfun]
  by_cases hj0 : j = 0
  · subst hj0
    rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_zero, ite_eq_left (rfl : (0 : ℕ) = 0)]
    calc ‖B • (L X - S • T) + (B * S + J) • T‖
        ≤ ‖B • (L X - S • T)‖ + ‖(B * S + J) • T‖ := norm_add_le _ _
      _ = B * ‖L X - S • T‖ + |B * S + J| * ‖T‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hB]
  · have h1 : ContDiff ℝ (j : ℕ∞) (fun Y => B • (L Y - S • T)) := hg.const_smul B
    have h2 : ContDiff ℝ (j : ℕ∞) (fun _ : Vec 2 => (B * S + J) • T) := contDiff_const
    have hsplit : iteratedFDeriv ℝ j (fun Y => B • (L Y - S • T) + (B * S + J) • T) X =
        B • iteratedFDeriv ℝ j (fun Y => L Y - S • T) X := by
      change iteratedFDeriv ℝ j ((fun Y => B • (L Y - S • T)) + fun _ => (B * S + J) • T) X = _
      rw [iteratedFDeriv_add_apply h1.contDiffAt h2.contDiffAt,
        iteratedFDeriv_const_of_ne hj0 ((B * S + J) • T), Pi.zero_apply, add_zero,
        iteratedFDeriv_const_smul_apply' (a := B) (f := fun Y => L Y - S • T) hg.contDiffAt]
    rw [hsplit, norm_smul, Real.norm_eq_abs, abs_of_nonneg hB]
    exact le_add_of_nonneg_right (ite_eq_right hj0).ge

section Data
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The operator data `Q` with the metric replaced by the identity (same `η`, drift, edges). -/
def flatData (Q : LiftOperatorData ι h D) : LiftOperatorData ι h D :=
  ⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩

end Data

section Setting
variable {ι : Type*} [hfin : Fintype ι] [hdec : DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [hfd : ∀ i, FiniteDimensional ℝ (h i)] [hcs : ∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {bm : ι → ι → ℝ} {Θ : ℝ}
include hfin hdec hfd hcs

omit hcs in
/-- The order-two letter is `C^r` in the slow variable through the reserved order. -/
theorem setting_diagonalMeanLetter_two_contDiff
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bm Θ)
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc)
    (α : DerivativeWord2 1) (l : Fin 2) (v : ι) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (r : ℕ) (hr : r ≤ K) :
    ContDiff ℝ (r : ℕ∞) (fun Y => diagonalMeanLetter Q Cc 2 2 α t Y l v v) := by
  let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
  have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
  have hreserve : K + (N + D) ≤ qs := by
    simpa only [Nat.add_assoc] using setting_ambient_output_supported P
  have hnR : 2 ≤ N + D := by
    have := P.N_ge
    have := P.D_ge
    omega
  have hc := (setting_diagonalMeanLetter_core P (K + D + 2) (max (k + 1) (L + 2)) (by omega)
    (by omega) Cc hseq K hreserve 2 le_rfl hnR).2.1 2 α l v v t ht
  exact hc.of_le (by exact_mod_cast (show r ≤ K + 1 by omega))

/-- **Metric stability against the flat cosine letter.** If the drift of `Q` is the cosine
shear `A(t) cos(2π z_⊥) e_∥` and the reserved jets of `G - I` are at most `CGI_r g λ^r`, the
order-two letter differs from `flatCosineLetter` by `C_r g λ^r` in its `r`-th slow jet. -/
theorem setting_diagonalMeanLetter_two_sub_flat
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bm Θ)
    (par' : Fin 2) (A : ℝ → ℝ)
    (hshear : ∀ t z, Q.v t z = cosineShear A t (z par'.rev) • basisVec par')
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun X' => fun i j : Fin 2 =>
          Q.G t X' i j - (if i = j then 1 else 0)) X‖ₑ) ≤ ENNReal.ofReal (CGI r * g * lam ^ r))
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc)
    (α : DerivativeWord2 1) (l : Fin 2) (v : ι) (r : ℕ) (hr : r ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => diagonalMeanLetter Q Cc 2 2 α t Y l v v -
        flatCosineLetter Q.η par' A a t α l • ContinuousLinearMap.id ℝ (h v)) X‖ ≤
      pairedMeanFluxWordBudget 2 r
        (pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI) Cw CGI *
          g * lam ^ r := by
  let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
  have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
  have hqs : K + 4 * (0 + 1) * (N + D) ^ 2 ≤ qs := zeroEdge_qs_le P rfl
  have hnR : 2 ≤ N + D := by
    have := P.N_ge
    have := P.D_ge
    omega
  have P0 := isLiftSetting_zeroEdge P par' (cosineShear A) hshear
    (fun t _ => cosineShear_contDiff A t) (fun t _ => cosineShear_periodic A t)
    (fun t _ => cosineShear_mean_zero A t)
    (qs' := K + 4 * (0 + 1) * (N + D) ^ 2) (qf' := max k (L + 2) + 0 * D + 2 * N + 2 * D)
    rfl rfl
  have Pf : IsLiftSetting (flatData (zeroEdgeData Q)) π a b e ν B ρ E ℓ dstar εc lam par'
      (cosineShear A) 0 N K k L (K + 4 * (0 + 1) * (N + D) ^ 2)
      (max k (L + 2) + 0 * D + 2 * N + 2 * D) (identityMetricJetBudget CG) Cw Cj bm Θ :=
    setting_identity_metric P0
  obtain ⟨Ci, hseqi⟩ := AVRegularity.Providers.cycle_lift_exists N K k L D 0
    (identityMetricJetBudget CG) Cw Cj (flatData (zeroEdgeData Q)) π a b e ν B ρ E ℓ dstar εc
    lam par' (cosineShear A) _ _ bm Θ Pf
  have hseq0 := isLiftSequence_zeroEdge Q _ _ a b N H Cc hseq
  have hb := setting_paired_mean_flux_original_reserve P0 Cc Ci hseq0 hseqi g hg CGI
    (fun r' hr' => hGI r' (hr'.trans hqs)) 2 le_rfl hnR 1 le_rfl (by omega) α r hr t ht l X 0 v v
  rw [ite_eq_left (rfl : v = v), mul_one, show 2 - 1 - 1 + r = r by omega] at hb
  have hfun : (fun Y => diagonalMeanLetter Q Cc 2 2 α t Y l v v -
      flatCosineLetter Q.η par' A a t α l • ContinuousLinearMap.id ℝ (h v)) =
      fun Y => diagonalMeanFluxCoefficient Q Cc 2 l 1 α t Y 0 v v -
        diagonalMeanFluxCoefficient (flatData (zeroEdgeData Q)) Ci 2 l 1 α t Y 0 v v := by
    funext Y
    have e1 := diagonalMeanLetter_two_eq (Q := Q) Cc α t Y l v v
    have e2 := diagonalMeanLetter_two_eq (Q := flatData (zeroEdgeData Q)) Ci α t Y l v v
    have e3 : diagonalMeanLetter (flatData (zeroEdgeData Q)) Ci 2 2 α t Y l v v =
        flatCosineLetter Q.η par' A a t α l • ContinuousLinearMap.id ℝ (h v) :=
      flat_diagonalMeanLetter_two Pf (fun _ _ _ _ => rfl) A (fun _ _ => rfl) _ _ Ci hseqi
        α t ht Y l v
    rw [e1, ← e3, e2]
  rw [hfun]
  exact hb

/-- **The order-two letter plus a constant.** For `B' ≥ 0` and any constant `J`, the slow jets
of `B' • letter + J • id` are at most `B' C_r g λ^r`, plus, for the value only, the size of the
constant `B' • flatCosineLetter + J`. -/
theorem setting_diagonalMeanLetter_two_add_const
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj bm Θ)
    (par' : Fin 2) (A : ℝ → ℝ)
    (hshear : ∀ t z, Q.v t z = cosineShear A t (z par'.rev) • basisVec par')
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun X' => fun i j : Fin 2 =>
          Q.G t X' i j - (if i = j then 1 else 0)) X‖ₑ) ≤ ENNReal.ofReal (CGI r * g * lam ^ r))
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc)
    (α : DerivativeWord2 1) (l : Fin 2) (v : ι) (r : ℕ) (hr : r ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) (B' J s : ℝ) (hB' : 0 ≤ B')
    (hs : |B' * flatCosineLetter Q.η par' A a t α l + J| ≤ s) :
    ‖iteratedFDeriv ℝ r (fun Y => B' • diagonalMeanLetter Q Cc 2 2 α t Y l v v +
        J • ContinuousLinearMap.id ℝ (h v)) X‖ ≤
      B' * (pairedMeanFluxWordBudget 2 r
        (pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI) Cw CGI *
          g * lam ^ r) + (if r = 0 then s else 0) := by
  have hcont := setting_diagonalMeanLetter_two_contDiff P Cc hseq α l v t ht r hr
  have h1 := norm_iteratedFDeriv_smul_add_const_le r
    (fun Y => diagonalMeanLetter Q Cc 2 2 α t Y l v v) (ContinuousLinearMap.id ℝ (h v)) B'
    (flatCosineLetter Q.η par' A a t α l) J hB' hcont X
  have h2 := setting_diagonalMeanLetter_two_sub_flat P par' A hshear g hg CGI hGI Cc hseq α l v
    r hr t ht X
  refine h1.trans (add_le_add (mul_le_mul_of_nonneg_left h2 hB') ?_)
  by_cases hr0 : r = 0
  · rw [ite_eq_left hr0, ite_eq_left hr0]
    calc |B' * flatCosineLetter Q.η par' A a t α l + J| * ‖ContinuousLinearMap.id ℝ (h v)‖
        ≤ s * 1 := mul_le_mul hs ContinuousLinearMap.norm_id_le (norm_nonneg _)
          ((abs_nonneg _).trans hs)
      _ = s := mul_one s
  · exact le_of_eq (by rw [ite_eq_right hr0, ite_eq_right hr0])

end Setting

end AVRegularity.CycleComparison.Diagonal
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Diagonal

/-! The cell-level core of clause 4 of `cycle_comparison`: on the lift window of an odd pulse `k`,
the order-two diagonal letter of the pulse lift, scaled by `B`, plus the reference flux `J`, has
`r`-th slow jets at most `C B g λ^r`, plus, for the value only, the switching price
`μ H_* M_k(ℓ² t₀)` of the zero-start memory at the start `t₀` of the window.

The proof combines identical-history metric stability against the flat cosine letter
(`setting_diagonalMeanLetter_two_sub_flat`, with `g` the size of the reserved jets of `G - I`)
with the exact identity `B · (flat letter) + J = μ H_* p_k e^{-μ(…)} M_k(ℓ²t₀) Π_k` on the
window (`pulse_flat_add_refFlux`). The constant is `C = ∑_{r ≤ K}` of the paired mean-flux budgets
of the lift library; it depends on the orders and the setting constants only. -/

open AVRegularity.CycleComparison.Lift

/-- The constant of `pulse_diagonal_two`. -/
def pulseDiagonalConst (N K k L D : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (CGI : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (K + 1), pairedMeanFluxWordBudget 2 r
    (pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI) Cw CGI

theorem pairedMeanFluxWordBudget_two_nonneg (N K k L D : ℕ) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) (CGI : ℕ → ℝ) (r : ℕ) :
    0 ≤ pairedMeanFluxWordBudget 2 r
      (pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI) Cw CGI :=
  pairedMeanFluxWordBudget_nonneg 2 r _ Cw CGI
    (fun n => pairedCoefficientScalarBudget_nonneg _ _ _ _ _ n _ _ _ _)

theorem pulseDiagonalConst_nonneg (N K k L D : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (CGI : ℕ → ℝ) : 0 ≤ pulseDiagonalConst N K k L D CG Cw Cj CGI :=
  Finset.sum_nonneg (fun r _ => pairedMeanFluxWordBudget_two_nonneg N K k L D CG Cw Cj CGI r)

theorem pairedMeanFluxWordBudget_le_pulseDiagonalConst (N K k L D : ℕ) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) (CGI : ℕ → ℝ) (r : ℕ) (hr : r ≤ K) :
    pairedMeanFluxWordBudget 2 r
        (pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI) Cw CGI ≤
      pulseDiagonalConst N K k L D CG Cw Cj CGI := by
  unfold pulseDiagonalConst
  exact Finset.single_le_sum
    (f := fun r => pairedMeanFluxWordBudget 2 r
      (pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI) Cw CGI)
    (fun r _ => pairedMeanFluxWordBudget_two_nonneg N K k L D CG Cw Cj CGI r)
    (Finset.mem_range.mpr (by omega))

/-- **The order-two diagonal letter of a pulse against the reference flux**, with the explicit
constant `pulseDiagonalConst`. -/
theorem pulse_diagonal_two_core {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
    {N K k L D H : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} (CGI : ℕ → ℝ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
    {ν B ρ lam : ℝ} {kp : ℤ} {edge : ConstituentEdges D h} {π : ι → ℝ}
    {t₀ t₁ E dstar εc : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ} {qs qf : ℕ} {b : ι → ι → ℝ}
    {Θ : ℝ} (g : ℝ) (hζ : IsFastProfile ζ) (hΛ : 1 ≤ Λ) (hk : Odd kp)
    (P : IsLiftSetting (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge) π t₀ t₁
      (ocEpsilon q Λ m) ν B ρ E (ocEll q Λ m ν) dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    (hg : 0 ≤ g)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc t₀ t₁, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun X' => fun i j : Fin 2 =>
          (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge).G t X' i j -
            (if i = j then 1 else 0)) X‖ₑ) ≤ ENNReal.ofReal (CGI r * g * lam ^ r))
    (hwin : ∀ t ∈ Set.Icc t₀ t₁, ocEll q Λ m ν ^ 2 * t ∈ ocPulseWindow α q Λ m kp)
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge) (K + D + 2)
      (max (k + 1) (L + 2)) t₀ t₁ N H Cc)
    (α' : DerivativeWord2 1) (l : Fin 2) (v : ι) (j : ℕ) (hj : j ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ t₁) (X : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun X' =>
        B • LiftMeanEntrywise.diagonalMeanLetter
            (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge) Cc 2 2 α' t X' l v v +
          ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) l (α' 0) •
            ContinuousLinearMap.id ℝ (h v)) X‖ ≤
      pulseDiagonalConst N K k L D CG Cw Cj CGI * B * g * lam ^ j +
        (if j = 0 then ocMu q Λ m ν * ocHStar α q Λ m ν *
          ocPulseMemory α q Λ ζ m ν kp (ocEll q Λ m ν ^ 2 * t₀) else 0) := by
  have hshear : ∀ s z, (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge).v s z =
      cosineShear (EntryWeakProofs.pulseShearAmplitude α q Λ m ζ ν kp) s
          (z (EntryWeakProofs.pulseParallel kp).rev) •
        basisVec (EntryWeakProofs.pulseParallel kp) :=
    fun s z => EntryWeakProofs.normalizedPulseDrift_shear (α := α) (q := q) (m := m) (ζ := ζ)
      hΛ P.ν_pos hk s z
  have hs : |B * flatCosineLetter (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge).η
        (EntryWeakProofs.pulseParallel kp) (EntryWeakProofs.pulseShearAmplitude α q Λ m ζ ν kp)
        t₀ t α' l + ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) l (α' 0)| ≤
      ocMu q Λ m ν * ocHStar α q Λ m ν *
        ocPulseMemory α q Λ ζ m ν kp (ocEll q Λ m ν ^ 2 * t₀) :=
    pulse_flat_add_refFlux_abs_le hΛ hζ P.ν_pos P.B_pos hk ht.1 (hwin t ht) α' l
  have hbound := setting_diagonalMeanLetter_two_add_const P
    (EntryWeakProofs.pulseParallel kp) (EntryWeakProofs.pulseShearAmplitude α q Λ m ζ ν kp)
    hshear g hg CGI hGI Cc hseq α' l v j hj t ht X B
    (ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) l (α' 0)) _ P.B_pos.le hs
  have hlam : 0 ≤ lam := by
    rw [P.lam_eq]
    exact (div_pos P.ρ_pos P.E_pos).le
  have hW := pairedMeanFluxWordBudget_le_pulseDiagonalConst N K k L D CG Cw Cj CGI j hj
  have hBg : 0 ≤ B * g * lam ^ j := mul_nonneg (mul_nonneg P.B_pos.le hg) (pow_nonneg hlam j)
  refine hbound.trans (add_le_add ?_ le_rfl)
  calc B * (pairedMeanFluxWordBudget 2 j
        (pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI) Cw CGI *
          g * lam ^ j)
      = pairedMeanFluxWordBudget 2 j
          (pairedCoefficientScalarBudget K (max k (L + 2)) D (N + D) N CG Cw Cj CGI) Cw CGI *
            (B * g * lam ^ j) := by ring
    _ ≤ pulseDiagonalConst N K k L D CG Cw Cj CGI * (B * g * lam ^ j) :=
        mul_le_mul_of_nonneg_right hW hBg
    _ = pulseDiagonalConst N K k L D CG Cw Cj CGI * B * g * lam ^ j := by ring

/-- **The order-two diagonal letter of a pulse against the reference flux**.
On the lift window of an odd pulse `k`, for a lift sequence
starting at `t₀`, the order-two diagonal letter scaled by `B` plus the reference flux has slow
jets at most `C B g λ^j`, plus the switching price `μ H_* M_k(ℓ² t₀)` in the value. Here `g`
bounds the reserved jets of `G - I`. -/
theorem pulse_diagonal_two (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (CGI : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
        (ν B ρ lam : ℝ) (kp : ℤ) (edge : ConstituentEdges D h) (π : ι → ℝ)
        (t₀ t₁ E dstar εc : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ) (b : ι → ι → ℝ)
        (Θ g : ℝ),
        IsFastProfile ζ → 1 ≤ Λ → Odd kp →
        IsLiftSetting (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge) π t₀ t₁ (ocEpsilon q Λ m)
          ν B ρ E (ocEll q Λ m ν) dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
        0 ≤ g →
        (∀ r, r ≤ qs →
          (⨆ t ∈ Set.Icc t₀ t₁, ⨆ X : Vec 2,
            ‖iteratedFDeriv ℝ r (fun X' => fun i j : Fin 2 =>
              (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge).G t X' i j -
                (if i = j then 1 else 0)) X‖ₑ)
            ≤ ENNReal.ofReal (CGI r * g * lam ^ r)) →
        (∀ t ∈ Set.Icc t₀ t₁, ocEll q Λ m ν ^ 2 * t ∈ ocPulseWindow α q Λ m kp) →
        ∀ Cc : ℕ → ℕ → LiftCoeff ι h,
          IsLiftSequence (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge) (K + D + 2)
            (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
          ∀ (α' : DerivativeWord2 1) (l : Fin 2) (v : ι) (j : ℕ), j ≤ K →
            ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
            ‖iteratedFDeriv ℝ j (fun X' =>
                B • LiftMeanEntrywise.diagonalMeanLetter
                    (pulseLiftData α q Λ m ζ φ hφ ν B ρ lam kp edge) Cc 2 2 α' t X' l v v +
                  ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) l (α' 0) •
                    ContinuousLinearMap.id ℝ (h v)) X‖ ≤
              C * B * g * lam ^ j +
                (if j = 0 then ocMu q Λ m ν * ocHStar α q Λ m ν *
                  ocPulseMemory α q Λ ζ m ν kp (ocEll q Λ m ν ^ 2 * t₀) else 0) := by
  refine ⟨pulseDiagonalConst N K k L D CG Cw Cj CGI,
    pulseDiagonalConst_nonneg N K k L D CG Cw Cj CGI, ?_⟩
  intro ι _ _ h _ _ _ _ α q Λ m ζ φ hφ ν B ρ lam kp edge π t₀ t₁ E dstar εc par V qs qf b Θ g
    hζ hΛ hk P hg hGI hwin Cc hseq α' l v j hj t ht X
  exact pulse_diagonal_two_core CGI g hζ hΛ hk P hg hGI hwin Cc hseq α' l v j hj t ht X

end AVRegularity.CycleComparison.Diagonal
end
