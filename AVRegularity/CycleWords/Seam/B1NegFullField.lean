-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Seam.B1PlainStage
public import AVRegularity.CycleWords.Seam.OldAdjointIdentification
public import AVRegularity.CycleWords.Seam.LetterTransposeNorm
import AVRegularity.CycleWords.Seam.S3bRoughCore
import AVRegularity.CycleJoint.PlaneJetMultiplierSuperposition
import AVRegularity.Weighted.WordNativeSolutionPack
import AVRegularity.CycleWords.MixedWords.Discard.FullFieldProved
public import AVRegularity.CycleWords.MixedWords.Discard.BlochBridge
public import AVRegularity.CycleWords.MixedWords.Discard.Pair
import AVRegularity.CycleWords.MixedWords.Discard.PlainPassStage
import AVRegularity.CycleWords.MixedWords.Discard.WeakContFluxTerm
import AVRegularity.CycleWords.MixedWords.RetainedAmplitudeFactor
import AVRegularity.CycleWords.Seam.B1PlainNeg

@[expose] public noncomputable section

section
open MeasureTheory Homogenization Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! **The level claim of the adjoint word chain** (item E of the adjoint chain interface).
For a word chain on `[a, b]` with zero data above level `0`, every level `j`, every intermediate
time `t`, every weight `p` and every test order `m ≥ ∑_{i<j} d_i + 1` (within the fast reserve):

`|⟨u_j(t), Φ⟩_π| ≤ C_j Θ_{<j} P^{Q_j} (1 + (t - a))^{Q_j} ‖Φ‖_{1,m;-p} ‖f‖_{2;p+∑_{i<j} K_i}`

for every rapidly decaying test family `Φ`, from a scalar reversed-adjoint bound with constants
`Ca k p` and powers `Qa k` (the package's `neg_adjoint`). The constant `C_j = levelC` and the power
`Q_j = levelQ` are explicit in the orders, the slow degrees, the fast reserve, the sign flags and
`Ca, Qa`; the power does not depend on `p`. -/

section
/-- A word quantity at the `i`-th letter, extended by `e` beyond the word. -/
def wordAt {N : ℕ} {α : Type*} (f : Fin N → α) (e : α) (i : ℕ) : α :=
  if hi : i < N then f ⟨i, hi⟩ else e

theorem wordAt_of_lt {N : ℕ} {α : Type*} (f : Fin N → α) (e : α) {i : ℕ} (hi : i < N) :
    wordAt f e i = f ⟨i, hi⟩ := by
  simp [wordAt, hi]

/-- The constant of the weighted bound of the transposed letter, without the amplitude. -/
def letterNormConst (n d J Ks : ℕ) (pos : Bool) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * ((n + d).factorial : ℝ) * letterTransposeConst n d J Ks pos 1

theorem letterTransposeConst_flag (n d J Ks : ℕ) (pos : Bool) (ζ : ℝ) :
    letterTransposeConst n d J Ks pos ζ =
      letterTransposeConst n d J Ks pos 1 * (if pos then ζ else 1) := by
  unfold letterTransposeConst
  split_ifs <;> ring

theorem letterNormConst_nonneg (n d J Ks : ℕ) (pos : Bool) : 0 ≤ letterNormConst n d J Ks pos :=
  mul_nonneg (by positivity) (letterTransposeConst_nonneg _ _ _ _ _ _ zero_le_one)

/-- The power of the level claim. -/
def levelQ (Qa : ℕ → ℕ) (dd : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, m => Qa m
  | j + 1, m => levelQ Qa dd j (m - dd j) + Qa m + 1

/-- The constant of the level claim. -/
def levelC (Ca : ℕ → ℕ → ℝ) (dd KK : ℕ → ℕ) (Lc : ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0, m, p => Real.sqrt (m + 1) * Ca m p
  | j + 1, m, p => levelC Ca dd KK Lc j (m - dd j) (p + KK j) * Lc j (m - dd j) *
      (Real.sqrt (m + 1) * Ca m p)

theorem levelC_nonneg (Ca : ℕ → ℕ → ℝ) (hCa : ∀ k p, 0 ≤ Ca k p) (dd KK : ℕ → ℕ)
    (Lc : ℕ → ℕ → ℝ) (hLc : ∀ j n, 0 ≤ Lc j n) :
    ∀ j m p, 0 ≤ levelC Ca dd KK Lc j m p
  | 0, m, p => mul_nonneg (Real.sqrt_nonneg _) (hCa m p)
  | j + 1, m, p => mul_nonneg (mul_nonneg (levelC_nonneg Ca hCa dd KK Lc hLc j _ _) (hLc _ _))
      (mul_nonneg (Real.sqrt_nonneg _) (hCa m p))

/-- The amplitude of the first `j` letters. -/
def levelTheta (θ : ℕ → ℝ) (j : ℕ) : ℝ := ∏ i ∈ Finset.range j, θ i

theorem levelTheta_nonneg (θ : ℕ → ℝ) (hθ : ∀ i, 0 ≤ θ i) (j : ℕ) : 0 ≤ levelTheta θ j :=
  Finset.prod_nonneg fun i _ => hθ i

section Level

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

/-- **Level `0`** of the claim. -/
theorem wordChain_level_zero_bound (hD : 2 ≤ D) (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (letters : Fin N → CycleLetter ι h D) (a b : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t)) (g : ℝ)
    (hg0 : 0 ≤ g) (hg : g ≤ 1 / 32) (hGn : IsMetricNearIdentity (fun t _ => G t) g)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    {η : ℝ} (hη : 0 < η) (Cvj : ℕ → ℝ)
    (hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ Cvj j)
    (M : ℝ) (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2) (ϖ δ P : ℝ) (Ca : ℕ → ℕ → ℝ) (Qa : ℕ → ℕ)
    (hadj : ∀ (k p : ℕ) (s t : ℝ), a ≤ s → s ≤ t → t ≤ b →
      ∀ (f : ∀ _ : Unit, PlaneHk Set.univ k ℝ)
        (u : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ k ℝ)
        (w : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (k + 1) ℝ),
        IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => k) (-t) (-s)
          (fun τ z => -(v (-τ) z)) f (fun _ _ _ => 0) u w →
        weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
            (fun x a w' => planeJetOrder (u 0 x (-s)) a w') ≤
          ENNReal.ofReal (Ca k p * P ^ Qa k * (1 + (t - s)) ^ Qa k) *
            weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
              (fun x a w' => planeJetOrder (f x) a w'))
    (X₀ : Vec 2) (κ : Fin (N + 1) → ι → ℕ) (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (U : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (Uw : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hsol : IsPlaneChain (wordChainData G letters X₀ δ) κ a b v f (fun _ _ _ => 0) U Uw)
    (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (Φ : ∀ x, PlaneHk Set.univ m (h x)) :
    ENNReal.ofReal |∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κ 0 x) (U 0 x t))
        (planeHkValueOperator m (Φ x))| ≤
      ENNReal.ofReal (Real.sqrt (m + 1) * Ca m p * P ^ Qa m * (1 + (t - a)) ^ Qa m) *
        weightedJetNorm π (-(p : ℝ)) m ϖ 1 (fun x i w z => planeJetOrder (Φ x) i w z) *
        weightedJetNorm π (p : ℝ) 0 ϖ 1 (fun x i w z => planeJetOrder (f x) i w z) := by
  set B : ∀ x, OrthonormalBasis (Fin (Module.finrank ℝ (h x))) ℝ (h x) :=
    fun x => stdOrthonormalBasis ℝ (h x)
  choose ψ ψw hψ using fun x (e : Fin (Module.finrank ℝ (h x))) =>
    exists_reversedAdjoint G hG g hg0 hg hGn v hv hvs hη Cvj hvj m ht.1
      (planeHkCoord (B x e) (Φ x))
  have hfrom : IsPlaneChainFrom (wordChainData G letters X₀ δ) κ a b v (wordLevelDatum κ f)
      (fun _ _ _ => 0) U Uw := hsol
  have hrest := CycleJointProofs.planeChainFrom_restart_subwindow _ κ a b a t le_rfl ht.1 ht.2
    v _ _ U Uw hfrom
  have hU0 : ∀ x, U 0 x a = f x := fun x => by
    have h0 := hfrom.2.2.2.1 ((0 : Fin (N + 1)), x)
    simpa only [wordLevelDatum_zero] using h0
  have hdual := wordChain_initial_vector_duality hD G hG letters X₀ δ κ a t ht.1 v hv M hb
    (fun p => U p.1 p.2 a) (fun p => U p.1 p.2) (fun p => Uw p.1 p.2) hrest π B m hm Φ ψ ψw hψ
  have hdual' : ∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κ 0 x) (U 0 x t))
      (planeHkValueOperator m (Φ x)) = ∑ x, (π x)⁻¹ * inner ℝ
        (planeHkValueOperator (κ 0 x) (f x))
        (planeHkValueOperator m (planeHkAssemble (B x) (fun e => ψ x e 0 () (-a)))) := by
    refine hdual.trans (Finset.sum_congr rfl fun x _ => ?_)
    rw [hU0 x]
  rw [hdual']
  have hpair := weighted_value_pairing_le π hπ f
    (fun x => planeHkAssemble (B x) (fun e => ψ x e 0 () (-a))) (p : ℝ) ϖ
  have hvec := reversedAdjoint_vector_bound π B G v ϖ P Ca Qa hadj m p ht.2 Φ ψ ψw hψ a le_rfl
    ht.1
  refine hpair.trans ?_
  calc weightedJetNorm π (p : ℝ) 0 ϖ 1 (fun x i w z => planeJetOrder (f x) i w z) *
        weightedJetNorm π (-(p : ℝ)) m ϖ 1 (fun x i w z =>
          planeJetOrder (planeHkAssemble (B x) (fun e => ψ x e 0 () (-a))) i w z)
      ≤ weightedJetNorm π (p : ℝ) 0 ϖ 1 (fun x i w z => planeJetOrder (f x) i w z) *
          (ENNReal.ofReal (Real.sqrt (m + 1)) *
            ENNReal.ofReal (Ca m p * P ^ Qa m * (1 + (t - a)) ^ Qa m) *
            weightedJetNorm π (-(p : ℝ)) m ϖ 1 (fun x i w z => planeJetOrder (Φ x) i w z)) :=
        mul_le_mul_right hvec _
    _ = _ := by
        rw [show Real.sqrt (m + 1) * Ca m p * P ^ Qa m * (1 + (t - a)) ^ Qa m =
            Real.sqrt (m + 1) * (Ca m p * P ^ Qa m * (1 + (t - a)) ^ Qa m) by ring,
          ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
        ring

end Level
end

/-! **The step of the level claim**: from the claim at level `j` (any constants `C_j`, powers
`Q_j` and datum norms `F_j`) to level `j + 1`, through the one-step duality, the weighted bound of
the transposed letter and the vector reversed-adjoint bound. -/

section
theorem ennreal_chain_le {E T Ψ A F : ℝ≥0∞} {x y z w : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (h1 : E ≤ ENNReal.ofReal x * T * F) (h2 : T ≤ ENNReal.ofReal y * Ψ)
    (h3 : Ψ ≤ ENNReal.ofReal z * ENNReal.ofReal w * A) :
    E ≤ ENNReal.ofReal (x * y * z * w) * A * F := by
  calc E ≤ ENNReal.ofReal x * T * F := h1
    _ ≤ ENNReal.ofReal x * (ENNReal.ofReal y * (ENNReal.ofReal z * ENNReal.ofReal w * A)) * F := by
        gcongr
        exact h2.trans (mul_le_mul_right h3 _)
    _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hx hy) hz), ENNReal.ofReal_mul
          (mul_nonneg hx hy), ENNReal.ofReal_mul hx]
        ring

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

/-- The transposed-letter integrand as an `L²` pairing with the transposed carrier. -/
theorem letterTranspose_pairing_eq {σ : Type*} (π : ι → ℝ) (L : CycleLetter ι h D) (κ : σ → ℕ)
    (a' b' : ι → σ) (lo : ℕ) (X₀ : Vec 2) (δ s : ℝ) (n d : ℕ)
    (Ψ : ∀ v, PlaneHk Set.univ (n + d) (h v)) (hreg : LetterTermRegular L lo X₀ δ s n d Ψ)
    {K : ι → ℕ} (W : ∀ u, PlaneHk Set.univ (K u) (h u)) :
    ∑ u, (π u)⁻¹ * ∫ z, inner ℝ ((W u).toFunction.jet (valueIndex2 (K u)) z)
        (letterTransposeJet π L κ a' b' lo X₀ δ s n d (fun v => (Ψ v).toFunction.jet) u
          (valueIndex2 n) z) =
      ∑ u, (π u)⁻¹ * inner ℝ (planeHkValueOperator (K u) (W u))
        (planeHkValueOperator n (letterTransposeHk π L κ a' b' lo X₀ δ s n d Ψ hreg u)) := by
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1
  rw [L2.inner_def]
  refine (integral_congr_ae ?_).symm
  filter_upwards [planeJetL2_ae (W u) (valueIndex2 _),
    planeJetL2_ae (letterTransposeHk π L κ a' b' lo X₀ δ s n d Ψ hreg u) (valueIndex2 n),
    letterTransposeHk_jet_ae π L κ a' b' lo X₀ δ s n d Ψ hreg u (valueIndex2 n)] with z h1 h2 h3
  rw [planeHkValueOperator_eq_planeJetL2, planeHkValueOperator_eq_planeJetL2, h1, h2, h3]

omit [Fintype ι] [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
/-- The time integral of an integrand bounded almost everywhere. -/
theorem ofReal_abs_intervalIntegral_le {g : ℝ → ℝ} {a t : ℝ} (hat : a ≤ t) {Bd : ℝ≥0∞}
    (hpt : ∀ᵐ r ∂volume.restrict (Set.Ioc a t), ‖g r‖ₑ ≤ Bd) :
    ENNReal.ofReal |∫ r in a..t, g r| ≤ Bd * ENNReal.ofReal (t - a) := by
  rw [intervalIntegral.integral_of_le hat, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ((lintegral_mono_ae hpt).trans
    (le_of_eq ?_))
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]

theorem letterNorm_eq (n d J Ks : ℕ) (pos : Bool) (ζ θ : ℝ) :
    ((n + 1 : ℕ) : ℝ) * ((n + d).factorial : ℝ) * (letterTransposeConst n d J Ks pos ζ * θ) =
      letterNormConst n d J Ks pos * (θ * (if pos then ζ else 1)) := by
  rw [letterTransposeConst_flag]
  unfold letterNormConst
  ring

theorem step_constants_le {Cj Lθ sq Ca P r t a : ℝ} (Qj Qa : ℕ) (hCj : 0 ≤ Cj) (hLθ : 0 ≤ Lθ)
    (hsq : 0 ≤ sq) (hCa : 0 ≤ Ca) (hP : 0 ≤ P) (har : a ≤ r) (hrt : r ≤ t) :
    Cj * P ^ Qj * (1 + (r - a)) ^ Qj * Lθ * sq * (Ca * P ^ Qa * (1 + (t - r)) ^ Qa) ≤
      Cj * Lθ * (sq * Ca) * P ^ Qj * P ^ Qa * (1 + (t - a)) ^ (Qj + Qa) := by
  have h1 : (1 + (r - a)) ^ Qj ≤ (1 + (t - a)) ^ Qj :=
    pow_le_pow_left₀ (by linarith) (by linarith) Qj
  have h2 : (1 + (t - r)) ^ Qa ≤ (1 + (t - a)) ^ Qa :=
    pow_le_pow_left₀ (by linarith) (by linarith) Qa
  have hK : 0 ≤ Cj * Lθ * (sq * Ca) * P ^ Qj * P ^ Qa := by positivity
  calc _ = (Cj * Lθ * (sq * Ca) * P ^ Qj * P ^ Qa) *
        ((1 + (r - a)) ^ Qj * (1 + (t - r)) ^ Qa) := by ring
    _ ≤ (Cj * Lθ * (sq * Ca) * P ^ Qj * P ^ Qa) *
        ((1 + (t - a)) ^ Qj * (1 + (t - a)) ^ Qa) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (pow_nonneg (by linarith) _)
          (pow_nonneg (by linarith) _)) hK
    _ = _ := by rw [pow_add]

/-- **The step of the level claim.** -/
theorem wordChain_level_succ_bound (hD : 2 ≤ D) (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (letters : Fin N → CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : ∀ i, IsCycleLetter π (letters i) (Set.Icc a b ×ˢ Set.univ) J H)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t)) (g : ℝ)
    (hg0 : 0 ≤ g) (hg : g ≤ 1 / 32) (hGn : IsMetricNearIdentity (fun t _ => G t) g)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    {η : ℝ} (hη : 0 < η) (Cvj : ℕ → ℝ)
    (hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ Cvj j)
    (M : ℝ) (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2) (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hϖ1 : ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (P : ℝ) (hP : 1 ≤ P) (Ca : ℕ → ℕ → ℝ)
    (hCa : ∀ k p, 0 ≤ Ca k p) (Qa : ℕ → ℕ)
    (hadj : ∀ (k p : ℕ) (s t : ℝ), a ≤ s → s ≤ t → t ≤ b →
      ∀ (f : ∀ _ : Unit, PlaneHk Set.univ k ℝ)
        (u : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ k ℝ)
        (w : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (k + 1) ℝ),
        IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => k) (-t) (-s)
          (fun τ z => -(v (-τ) z)) f (fun _ _ _ => 0) u w →
        weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
            (fun x a w' => planeJetOrder (u 0 x (-s)) a w') ≤
          ENNReal.ofReal (Ca k p * P ^ Qa k * (1 + (t - s)) ^ Qa k) *
            weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
              (fun x a w' => planeJetOrder (f x) a w'))
    (X₀ : Vec 2) (κ : Fin (N + 1) → ι → ℕ) (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (U : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (Uw : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hsol : IsPlaneChain (wordChainData G letters X₀ (ζ * ϖ)) κ a b v f (fun _ _ _ => 0) U Uw)
    (hflux : ∀ (i : Fin N) (x : ι), ∃ S : ℝ → PlaneFluxL2 (h x),
      MemLp S 2 (volume.restrict (Set.Icc a b)) ∧
        ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ k, S r k =ᵐ[volume] fun z =>
          wordChainPreviousFlux letters X₀ (ζ * ϖ) κ (fun p => Uw p.1 p.2 r) (i.succ, x) r z k)
    (jj : Fin N) (lowj : ℕ) (hlowj : 1 ≤ lowj) (Cj : ℕ → ℕ → ℝ) (hCj : ∀ n p, 0 ≤ Cj n p)
    (Qj : ℕ → ℕ) (Fj : ℕ → ℝ≥0∞)
    (ih : ∀ n : ℕ, lowj ≤ n → n ≤ J + 1 → ∀ (p : ℕ) (r : ℝ), r ∈ Set.Icc a b →
      ∀ T : ∀ x, PlaneHk Set.univ n (h x), (∀ x, IsRapidPlaneHk ϖ (T x)) →
        ENNReal.ofReal |∑ x, (π x)⁻¹ * inner ℝ
            (planeHkValueOperator (κ jj.castSucc x) (U jj.castSucc x r))
            (planeHkValueOperator n (T x))| ≤
          ENNReal.ofReal (Cj n p * P ^ Qj n * (1 + (r - a)) ^ Qj n) *
            weightedJetNorm π (-(p : ℝ)) n ϖ 1 (fun x i w z => planeJetOrder (T x) i w z) *
            Fj p)
    (n : ℕ) (hn : lowj ≤ n) (hnJ : n + (letters jj).order ≤ J + 1) (p : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (Φ : ∀ x, PlaneHk Set.univ (n + (letters jj).order) (h x))
    (hΦ : ∀ x, IsRapidPlaneHk ϖ (Φ x)) :
    ENNReal.ofReal |∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κ jj.succ x) (U jj.succ x t))
        (planeHkValueOperator (n + (letters jj).order) (Φ x))| ≤
      ENNReal.ofReal (Cj n (p + (letters jj).slow) *
          letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
          ((letters jj).theta * (if (letters jj).positive then ζ else 1)) *
          (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p) *
          P ^ (Qj n + Qa (n + (letters jj).order) + 1) *
          (1 + (t - a)) ^ (Qj n + Qa (n + (letters jj).order) + 1)) *
        weightedJetNorm π (-(p : ℝ)) (n + (letters jj).order) ϖ 1
          (fun x i w z => planeJetOrder (Φ x) i w z) *
        Fj (p + (letters jj).slow) := by
  have hd2 : 2 ≤ (letters jj).order := (hL jj).order_ge
  have hn1 : 1 ≤ n := hlowj.trans hn
  have hn1' : 1 ≤ n + (letters jj).order := by omega
  -- the reversed adjoint chains of the coordinates of the test
  set B : ∀ x, OrthonormalBasis (Fin (Module.finrank ℝ (h x))) ℝ (h x) :=
    fun x => stdOrthonormalBasis ℝ (h x)
  choose ψ ψw hψ using fun x (e : Fin (Module.finrank ℝ (h x))) =>
    exists_reversedAdjoint G hG g hg0 hg hGn v hv hvs hη Cvj hvj (n + (letters jj).order) ht.1
      (planeHkCoord (B x e) (Φ x))
  -- rapid decay of the assembled adjoint family
  set r₀ := 1 / (3 * Interior.negAdjointJetConstant Cvj (n + (letters jj).order) * (1 + (Real.sqrt η)⁻¹)) with hr₀def
  have hr₀ : 0 < r₀ := by
    have h1 := Interior.one_le_negAdjointJetConstant Cvj (n + (letters jj).order)
    have h2 : 0 < (Real.sqrt η)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hη)
    rw [hr₀def]
    positivity
  have hΨr : ∀ τ ∈ Set.Icc (-t) (-a), ∀ x,
      IsRapidPlaneHk ϖ (planeHkAssemble (B x) (fun e => ψ x e 0 () τ)) := fun τ hτ x =>
    rapid_assemble (B x) _ fun e => rapid_of_weightedFactorialNormSq hr₀ _ fun q =>
      reversedAdjoint_weighted_finite G hG v hv hvs hη Cvj hvj ϖ hϖ.le (n + (letters jj).order) q ht.1 _ (ψ x e)
        (ψw x e) (hψ x e) r₀ hr₀ le_rfl
        (weightedFactorialNormSq_ne_top_of_rapid _ (rapid_coord _ _ (hΦ x)) q r₀) τ hτ
  have hΨr' : ∀ r ∈ Set.Icc a t, ∀ x,
      IsRapidPlaneHk ϖ (planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))) := fun r hr =>
    hΨr (-r) ⟨neg_le_neg hr.2, neg_le_neg hr.1⟩
  -- the forward chain on `[a, t]`
  have hfrom : IsPlaneChainFrom (wordChainData G letters X₀ (ζ * ϖ)) κ a b v
      (wordLevelDatum κ f) (fun _ _ _ => 0) U Uw := hsol
  have hrest := CycleJointProofs.planeChainFrom_restart_subwindow _ κ a b a t le_rfl ht.1 ht.2
    v _ _ U Uw hfrom
  have hsub : Set.Icc a t ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl ht.2
  choose S hSl hS using hflux jj
  -- the almost-every-time facts of the letter
  have hregAE := letterTermRegular_ae π hπ (letters jj) a b J H (hL jj) ϖ ζ hϖ hϖ1 hζ hζ1 X₀ n (letters jj).order
    hnJ
  have hbndAE := letterTranspose_weightedJetNorm_le_ae π hπ (letters jj) a b J H (hL jj) ϖ ζ hϖ
    hϖ1 hζ hζ1 X₀ (fun q : Fin (N + 1) × ι => κ q.1 q.2) (fun x => (jj.succ, x))
    (fun u => (jj.castSucc, u)) n (letters jj).order hnJ
  have hrapAE := letterTransposeHk_rapid_ae π hπ (letters jj) a b J H (hL jj) ϖ ζ hϖ hϖ1 hζ hζ1
    X₀ (fun q : Fin (N + 1) × ι => κ q.1 q.2) (fun x => (jj.succ, x))
    (fun u => (jj.castSucc, u)) n (letters jj).order hnJ
  have hregΨ : ∀ r ∈ Set.Icc a t, ∀ x (i : JetIndex2 (n + (letters jj).order)), MemLp (fun z =>
      polynomialMomentRoot ϖ z ^ (letters jj).slow *
        ‖(planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))).toFunction.jet i z‖) 2 volume := by
    intro r hr x i
    have h1 := hΨr' r hr x (letters jj).slow i.1.val i.2
    simpa only [planeJetOrder, Nat.le_of_lt_succ i.1.isLt, dite_true, Fin.eta, Sigma.eta] using h1
  have hreg : ∀ᵐ r ∂volume.restrict (Set.Icc a t), LetterTermRegular (letters jj)
      (if (letters jj).positive then 1 else 0) X₀ (ζ * ϖ) r n (letters jj).order
      (fun x => planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hregAE,
      ae_restrict_mem measurableSet_Icc] with r hr hrmem
    exact hr _ (hregΨ r hrmem)
  -- the one-step duality
  have hempty : ∀ x u (o : Finset.Icc 2 D), (letters jj).order < o.1 → (letters jj).edge x u o = [] :=
    fun x u o ho => (hL jj).edge_order x u o ho
  have hdual := wordChain_letter_step_duality hD G hG letters X₀ (ζ * ϖ) κ a t ht.1 v hv M hb
    (fun q => U q.1 q.2 a) (fun q => U q.1 q.2) (fun q => Uw q.1 q.2) hrest jj S
    (fun x => (hSl x).mono_measure (Measure.restrict_mono hsub le_rfl))
    (fun x => ae_restrict_of_ae_restrict_of_subset hsub (hS x)) π hπ B n (letters jj).order (by omega) hempty Φ
    ψ ψw hψ hreg
  have hUa : ∀ x, U jj.succ x a = 0 := fun x => by
    have h0 := hfrom.2.2.2.1 (jj.succ, x)
    simpa only [wordLevelDatum_succ] using h0
  simp only [hUa, ContinuousLinearMap.map_zero, inner_zero_left, mul_zero, Finset.sum_const_zero,
    zero_sub] at hdual
  rw [hdual, abs_neg]
  -- the constants
  have hθζ : 0 ≤ (letters jj).theta * (if (letters jj).positive then ζ else 1) :=
    mul_nonneg (hL jj).theta_nonneg (by split <;> positivity)
  have hLθ : 0 ≤ letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
      ((letters jj).theta * (if (letters jj).positive then ζ else 1)) :=
    mul_nonneg (letterNormConst_nonneg _ _ _ _ _) hθζ
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hsq : 0 ≤ Real.sqrt (↑(n + (letters jj).order) + 1) := Real.sqrt_nonneg _
  have hK0 : 0 ≤ Cj n (p + (letters jj).slow) *
      (letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
        ((letters jj).theta * (if (letters jj).positive then ζ else 1))) *
      (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p) *
      P ^ Qj n * P ^ Qa (n + (letters jj).order) := by
    have := hCj n (p + (letters jj).slow)
    have := hCa (n + (letters jj).order) p
    positivity
  have hsubI : Set.Ioc a t ⊆ Set.Icc a b := Set.Ioc_subset_Icc_self.trans hsub
  refine (ofReal_abs_intervalIntegral_le ht.1 (Bd := ENNReal.ofReal
      (Cj n (p + (letters jj).slow) *
        (letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
          ((letters jj).theta * (if (letters jj).positive then ζ else 1))) *
        (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p) *
        P ^ Qj n * P ^ Qa (n + (letters jj).order) *
        (1 + (t - a)) ^ (Qj n + Qa (n + (letters jj).order)) ) *
      weightedJetNorm π (-(p : ℝ)) (n + (letters jj).order) ϖ 1
        (fun x i w z => planeJetOrder (Φ x) i w z) * Fj (p + (letters jj).slow)) ?_).trans ?_
  · -- the integrand, almost everywhere
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubI hregAE,
      ae_restrict_of_ae_restrict_of_subset hsubI hbndAE,
      ae_restrict_of_ae_restrict_of_subset hsubI hrapAE, ae_restrict_mem measurableSet_Ioc]
      with r hr1 hr2 hr3 hrI
    have hrab : r ∈ Set.Icc a b := hsubI hrI
    have hrat : r ∈ Set.Icc a t := Set.Ioc_subset_Icc_self hrI
    have hregr := hr1 _ (hregΨ r hrat)
    have hgr := letterTranspose_pairing_eq π (letters jj) (fun q : Fin (N + 1) × ι => κ q.1 q.2)
      (fun x => (jj.succ, x)) (fun u => (jj.castSucc, u))
      (if (letters jj).positive then 1 else 0) X₀ (ζ * ϖ) r n (letters jj).order
      (fun x => planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))) hregr
      (fun u => U jj.castSucc u r)
    beta_reduce at hgr
    have hih := ih n hn ((Nat.le_add_right n (letters jj).order).trans hnJ)
      (p + (letters jj).slow) r hrab _ (hr3 _ hregr fun x => hΨr' r hrat x)
    have hLb := hr2 _ hregr (p : ℝ) (letters jj).slow le_rfl
    have hvb := reversedAdjoint_vector_bound π B G v ϖ P Ca Qa hadj (n + (letters jj).order) p
      ht.2 Φ ψ ψw hψ r hrat.1 hrat.2
    have hcast : (-(((p + (letters jj).slow : ℕ) : ℝ))) = -((p : ℝ) + ((letters jj).slow : ℝ)) := by
      push_cast
      ring
    rw [hcast] at hih
    have h1 := hgr ▸ hih
    rw [← Real.enorm_eq_ofReal_abs] at h1
    have hx0 : 0 ≤ Cj n (p + (letters jj).slow) * P ^ Qj n * (1 + (r - a)) ^ Qj n := by
      have := hCj n (p + (letters jj).slow)
      have : 0 ≤ 1 + (r - a) := by linarith [hrat.1]
      positivity
    have hy0 : 0 ≤ ((n + 1 : ℕ) : ℝ) * ((n + (letters jj).order).factorial : ℝ) *
        (letterTransposeConst n (letters jj).order J (letters jj).slow (letters jj).positive ζ *
          (letters jj).theta) :=
      mul_nonneg (by positivity) (mul_nonneg (letterTransposeConst_nonneg _ _ _ _ _ _ hζ)
        (hL jj).theta_nonneg)
    refine (ennreal_chain_le hx0 hy0 hsq h1 hLb hvb).trans ?_
    refine mul_le_mul_left (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _) _
    rw [letterNorm_eq]
    exact step_constants_le _ _ (hCj _ _) hLθ hsq (hCa _ _) hP0 hrat.1 hrat.2
  · -- the time integration
    have hta : 0 ≤ t - a := by linarith [ht.1]
    have hX : 0 ≤ Cj n (p + (letters jj).slow) *
        (letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
          ((letters jj).theta * (if (letters jj).positive then ζ else 1))) *
        (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p) *
        P ^ Qj n * P ^ Qa (n + (letters jj).order) *
        (1 + (t - a)) ^ (Qj n + Qa (n + (letters jj).order)) :=
      mul_nonneg hK0 (pow_nonneg (by linarith) _)
    rw [mul_right_comm, mul_right_comm (ENNReal.ofReal _) _ (ENNReal.ofReal (t - a)),
      ← ENNReal.ofReal_mul hX]
    refine mul_le_mul_left (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _) _
    have h1 : (t - a) ≤ 1 + (t - a) := by linarith
    have hPP : P ^ Qj n * P ^ Qa (n + (letters jj).order) ≤
        P ^ (Qj n + Qa (n + (letters jj).order) + 1) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hP (Nat.le_succ _)
    have hC1 : 0 ≤ Cj n (p + (letters jj).slow) *
        (letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
          ((letters jj).theta * (if (letters jj).positive then ζ else 1))) *
        (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p) := by
      have := hCj n (p + (letters jj).slow)
      have := hCa (n + (letters jj).order) p
      positivity
    calc Cj n (p + (letters jj).slow) *
          (letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
            ((letters jj).theta * (if (letters jj).positive then ζ else 1))) *
          (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p) *
          P ^ Qj n * P ^ Qa (n + (letters jj).order) *
          (1 + (t - a)) ^ (Qj n + Qa (n + (letters jj).order)) * (t - a)
        = (Cj n (p + (letters jj).slow) *
            (letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
              ((letters jj).theta * (if (letters jj).positive then ζ else 1))) *
            (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p)) *
          (P ^ Qj n * P ^ Qa (n + (letters jj).order)) *
          ((1 + (t - a)) ^ (Qj n + Qa (n + (letters jj).order)) * (t - a)) := by ring
      _ ≤ (Cj n (p + (letters jj).slow) *
            (letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
              ((letters jj).theta * (if (letters jj).positive then ζ else 1))) *
            (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p)) *
          P ^ (Qj n + Qa (n + (letters jj).order) + 1) *
          (1 + (t - a)) ^ (Qj n + Qa (n + (letters jj).order) + 1) := by
          rw [pow_succ (1 + (t - a))]
          gcongr
      _ = _ := by ring
end

/-! **The level claim of the adjoint word chain**, by induction over the levels (item E of
the adjoint chain interface). The constants are `levelC`, `levelTheta` and `levelQ` of the word's
orders, slow degrees, sign flags and amplitudes; the power `levelQ` does not depend on the weight. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

/-- The orders of a word, extended by `0`. -/
def wordOrders (letters : Fin N → CycleLetter ι h D) : ℕ → ℕ :=
  wordAt (fun i => (letters i).order) 0

/-- The slow degrees of a word, extended by `0`. -/
def wordSlows (letters : Fin N → CycleLetter ι h D) : ℕ → ℕ :=
  wordAt (fun i => (letters i).slow) 0

/-- The amplitudes `θ_i` (times `ζ` for positive letters) of a word, extended by `1`. -/
def wordAmplitudes (letters : Fin N → CycleLetter ι h D) (ζ : ℝ) : ℕ → ℝ :=
  wordAt (fun i => (letters i).theta * (if (letters i).positive then ζ else 1)) 1

/-- The letter constants of a word. -/
def wordLetterConsts (letters : Fin N → CycleLetter ι h D) (J : ℕ) : ℕ → ℕ → ℝ :=
  fun j n => letterNormConst n (wordOrders letters j) J (wordSlows letters j)
    (wordAt (fun i => (letters i).positive) false j)

/-- **The level claim.** -/
theorem wordChain_level_bound (hD : 2 ≤ D) (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (letters : Fin N → CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : ∀ i, IsCycleLetter π (letters i) (Set.Icc a b ×ˢ Set.univ) J H)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t)) (g : ℝ)
    (hg0 : 0 ≤ g) (hg : g ≤ 1 / 32) (hGn : IsMetricNearIdentity (fun t _ => G t) g)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    {η : ℝ} (hη : 0 < η) (Cvj : ℕ → ℝ)
    (hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ Cvj j)
    (M : ℝ) (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2) (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hϖ1 : ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (P : ℝ) (hP : 1 ≤ P) (Ca : ℕ → ℕ → ℝ)
    (hCa : ∀ k p, 0 ≤ Ca k p) (Qa : ℕ → ℕ)
    (hadj : ∀ (k p : ℕ) (s t : ℝ), a ≤ s → s ≤ t → t ≤ b →
      ∀ (f : ∀ _ : Unit, PlaneHk Set.univ k ℝ)
        (u : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ k ℝ)
        (w : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (k + 1) ℝ),
        IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => k) (-t) (-s)
          (fun τ z => -(v (-τ) z)) f (fun _ _ _ => 0) u w →
        weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
            (fun x a w' => planeJetOrder (u 0 x (-s)) a w') ≤
          ENNReal.ofReal (Ca k p * P ^ Qa k * (1 + (t - s)) ^ Qa k) *
            weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
              (fun x a w' => planeJetOrder (f x) a w'))
    (X₀ : Vec 2) (κ : Fin (N + 1) → ι → ℕ) (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (U : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (Uw : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hsol : IsPlaneChain (wordChainData G letters X₀ (ζ * ϖ)) κ a b v f (fun _ _ _ => 0) U Uw)
    (hflux : ∀ (i : Fin N) (x : ι), ∃ S : ℝ → PlaneFluxL2 (h x),
      MemLp S 2 (volume.restrict (Set.Icc a b)) ∧
        ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ k, S r k =ᵐ[volume] fun z =>
          wordChainPreviousFlux letters X₀ (ζ * ϖ) κ (fun p => Uw p.1 p.2 r) (i.succ, x) r z k) :
    ∀ (j : ℕ) (hj : j ≤ N) (m : ℕ), (∑ i ∈ Finset.range j, wordOrders letters i) + 1 ≤ m →
      m ≤ J + 1 → ∀ (p : ℕ) (t : ℝ), t ∈ Set.Icc a b →
      ∀ Φ : ∀ x, PlaneHk Set.univ m (h x), (∀ x, IsRapidPlaneHk ϖ (Φ x)) →
        ENNReal.ofReal |∑ x, (π x)⁻¹ * inner ℝ
            (planeHkValueOperator (κ ⟨j, Nat.lt_succ_of_le hj⟩ x)
              (U ⟨j, Nat.lt_succ_of_le hj⟩ x t))
            (planeHkValueOperator m (Φ x))| ≤
          ENNReal.ofReal (levelC Ca (wordOrders letters) (wordSlows letters)
              (wordLetterConsts letters J) j m p * levelTheta (wordAmplitudes letters ζ) j *
              P ^ levelQ Qa (wordOrders letters) j m *
              (1 + (t - a)) ^ levelQ Qa (wordOrders letters) j m) *
            weightedJetNorm π (-(p : ℝ)) m ϖ 1 (fun x i w z => planeJetOrder (Φ x) i w z) *
            weightedJetNorm π ((p + ∑ i ∈ Finset.range j, wordSlows letters i : ℕ) : ℝ) 0 ϖ 1
              (fun x i w z => planeJetOrder (f x) i w z) := by
  have hLc : ∀ j n, 0 ≤ wordLetterConsts letters J j n := fun j n =>
    letterNormConst_nonneg _ _ _ _ _
  have hθ : ∀ i, 0 ≤ wordAmplitudes letters ζ i := by
    intro i
    unfold wordAmplitudes wordAt
    split_ifs
    · exact mul_nonneg (hL _).theta_nonneg (by split <;> positivity)
    · exact zero_le_one
  intro j
  induction j with
  | zero =>
    intro hj m hm hmJ p t ht Φ _
    have h0 := wordChain_level_zero_bound hD π hπ letters a b G hG g hg0 hg hGn v hv hvs hη Cvj
      hvj M hb ϖ (ζ * ϖ) P Ca Qa hadj X₀ κ f U Uw hsol m (by simpa using hm) p t ht Φ
    refine h0.trans (le_of_eq ?_)
    simp only [levelC, levelTheta, levelQ, Finset.prod_range_zero, Finset.sum_range_zero,
      add_zero, mul_one]
  | succ j ih =>
    intro hj m hm hmJ p t ht Φ hΦ
    set jj : Fin N := ⟨j, hj⟩ with hjjdef
    have hord : wordOrders letters j = (letters jj).order := wordAt_of_lt _ _ hj
    have hslow : wordSlows letters j = (letters jj).slow := wordAt_of_lt _ _ hj
    have hpos : wordAt (fun i => (letters i).positive) false j = (letters jj).positive :=
      wordAt_of_lt _ _ hj
    have hamp : wordAmplitudes letters ζ j =
        (letters jj).theta * (if (letters jj).positive then ζ else 1) := wordAt_of_lt _ _ hj
    rw [Finset.sum_range_succ, hord] at hm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + (letters jj).order := ⟨m - (letters jj).order, by omega⟩
    have hstep := wordChain_level_succ_bound hD π hπ letters a b J H hL G hG g hg0 hg hGn v hv
      hvs hη Cvj hvj M hb ϖ ζ hϖ hϖ1 hζ hζ1 P hP Ca hCa Qa hadj X₀ κ f U Uw hsol hflux jj
      ((∑ i ∈ Finset.range j, wordOrders letters i) + 1) (Nat.succ_le_succ (Nat.zero_le _))
      (fun n p => levelC Ca (wordOrders letters) (wordSlows letters)
        (wordLetterConsts letters J) j n p * levelTheta (wordAmplitudes letters ζ) j)
      (fun n p => mul_nonneg (levelC_nonneg Ca hCa _ _ _ hLc j n p)
        (levelTheta_nonneg _ hθ j))
      (levelQ Qa (wordOrders letters) j)
      (fun p => weightedJetNorm π ((p + ∑ i ∈ Finset.range j, wordSlows letters i : ℕ) : ℝ) 0 ϖ 1
        (fun x i w z => planeJetOrder (f x) i w z))
      (fun n hn hnJ p r hr T hT => ih (Nat.le_of_succ_le hj) n hn hnJ p r hr T hT)
      n (by omega) hmJ p t ht Φ hΦ
    beta_reduce at hstep
    refine hstep.trans (le_of_eq ?_)
    have hw : p + (letters jj).slow + ∑ i ∈ Finset.range j, wordSlows letters i =
        p + ∑ i ∈ Finset.range (j + 1), wordSlows letters i := by
      rw [Finset.sum_range_succ, hslow]
      ring
    rw [hw]
    congr 2
    congr 1
    simp only [levelC, levelQ, levelTheta, Finset.prod_range_succ, hslow, hamp,
      wordLetterConsts, hord, hpos, Nat.add_sub_cancel]
    ring
end

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # Quiet margin fibre bound: the quiet entrance quiet margin

`B1QuietMarginStatement`: on a frame whose first stretch `[a, a₁]`, `a₁ − a ≥ 1`, is quiet with zero
drift, the stage values at `a₁` (all levels) have `L²` norms at most
`C (1 + (a₁ − a))^Q (e^{−ρ(a₁ − a)} N_k + L)`, `ρ = (π/8)²/2`, with `N_k` the `H^{-k}` norms of the
stage values at `a` (`stageDatumNegSq`) and `L` their low band `|2πn + θ| < π/8`
(`stageDatumLowSq`).

`b1_quiet_margin_of_quietMode`: from `QuietModeStatement` on the frame cut at `a₁`
(`AmplitudeIdFrame.b1Cut`): every cell mode solves the triangular Duhamel system of the quiet margin, and
the `quietMode_scalar_bound` (output weight `1`, input weight `(1 + |y|²)^{-k}`) gives, per mode,
the factor `K₀ (1 + (a₁ − a))^{2M} e^{−(y₀/2)(a₁ − a)}`, with `y₀ = (π/8)²` on the modes
`|y| ≥ π/8` and `y₀ = 0` (and the weight dropped) on the low band. Then the sum over the modes.

For `N_w = 0` each mode is multiplied by its heat factor, and for a zero datum the bound reads
`0 ≤ 0`. The constants `C, Q` are chosen after the shape, `K_f` and `k`, and before the frame, the
frequency and `a₁`. -/

section
open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

universe u v

/-- **The quiet entrance quiet margin** (the statement). -/
def B1QuietMarginStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D m Kf k : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    wordReserveJstar (wordReserveKstar (Kf + k) (wordReserveN m Ks) d) d ≤ F.J →
    θ ∈ freqCube →
  ∀ a₁ : ℝ, F.a + 1 ≤ a₁ → a₁ ≤ F.b → Icc F.a a₁ ⊆ F.reg.quiet →
    (∀ t ∈ Icc F.a a₁, ∀ z, F.v t z = 0) →
    ∑ i : B1WIndex ι h Nw m Ks, cellNegSq 0 θ (stageScaled F θ i a₁) ≤
      ENNReal.ofReal (C * (1 + (a₁ - F.a)) ^ Q) *
        (ENNReal.ofReal (Real.exp (-((Real.pi / 8) ^ 2 / 2) * (a₁ - F.a))) *
            stageDatumNegSq F m Ks k θ +
          stageDatumLowSq F m Ks (Real.pi / 8) θ)

/-- **The quiet entrance quiet margin**, from `QuietModeStatement` on the cut frame. -/
theorem b1_quiet_margin_of_quietMode (hMq : QuietModeStatement.{u, v}) : B1QuietMarginStatement.{u, v} := by
  intro K
  obtain ⟨g₁, hg₁, hMK⟩ := hMq K
  refine ⟨g₁, hg₁, ?_⟩
  intro Nw D m Kf k d Ks pos
  obtain ⟨B, p, hB, hBQ⟩ := hMK Nw D m (Kf + k) d Ks pos
  set Mst : ℕ := b1wM Nw m Ks with hMst
  set L : ℝ := 1 + (Mst + 1) * B with hL
  set K0 : ℝ := (Mst + 1) * L ^ (2 * (Mst + 1)) * quietAbsorbConst (0 + 2 * p * Mst + k)
    with hK0
  have hL1 : 1 ≤ L := by
    rw [hL]; nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ Mst + 1) hB]
  have hK0p : 0 < K0 := by
    rw [hK0]; have := quietAbsorbConst_pos (0 + 2 * p * Mst + k); positivity
  refine ⟨K0, 2 * Mst, hK0p, ?_⟩
  intro ι _ h _ _ _ _ _ _ F θ hlet hJ hθ a₁ ha₁ ha₁b hqu hv0
  have hac : F.a ≤ a₁ := by linarith
  set Dq : ℝ := a₁ - F.a with hDqdef
  have hDq : 1 ≤ Dq := by rw [hDqdef]; linarith
  have hb : a₁ = F.a + Dq := by rw [hDqdef]; ring
  -- the bound for one mode
  have pn : ∀ y0 : ℝ, 0 ≤ y0 → ∀ n : Fin 2 → ℤ, y0 ≤ quietYSq θ n →
      (1 + quietYSq θ n) ^ 0 * ∑ i : B1WIndex ι h Nw m Ks, ‖stageMode F θ i n a₁‖ ^ 2 ≤
        K0 * (1 + Dq) ^ (2 * Mst) * Real.exp (-(y0 / 2) * Dq) *
          ∑ i' : B1WIndex ι h Nw m Ks, ((1 + quietYSq θ n) ^ k)⁻¹ *
            ‖stageMode F θ i' n F.a‖ ^ 2 := by
    intro y0 hy0 n hband
    obtain ⟨τ, hop, hT0, hint, hD⟩ := hBQ (F.b1Cut a₁ hac ha₁b) θ hlet hJ hθ F.a le_rfl hac
      hqu hv0 n
    have hint' : ∀ t ∈ Icc F.a (F.a + Dq), ∀ i, IntervalIntegrable (fun r =>
        Complex.exp (∫ s in r..t, quietLam F.G θ n s) *
          ∑ i', τ i i' r * stageMode F θ i' n r) volume F.a t := by
      rw [← hb]; exact hint
    have hD' : ∀ i, ∀ t ∈ Icc F.a (F.a + Dq), stageMode F θ i n t =
        Complex.exp (∫ r in F.a..t, quietLam F.G θ n r) * stageMode F θ i n F.a +
        ∫ r in F.a..t, Complex.exp (∫ s in r..t, quietLam F.G θ n s) *
          ∑ i', τ i i' r * stageMode F θ i' n r := by
      rw [← hb]; intro i t ht; exact hD t ht i
    have := quietMode_scalar_bound (fun i : B1WIndex ι h Nw m Ks => b1wSt i) (Mst := Mst)
      (fun i => (b1wSt_lt i).le) hB p k 0 (y0 := y0) (yq := quietYSq θ n) (Dq := Dq) hy0
      hband hDq (t₁ := F.a) (quietLam F.G θ n) (fun i t => stageMode F θ i n t) τ hop hT0
      (fun s t _ hs _ => by simpa using quietLam_exp_bound F.G F.piece.hGm θ n hs) hint' hD'
    rw [← hb] at this
    exact this
  -- the bound for one mode, in the two bands
  have hq0 : ∀ n, 0 ≤ quietYSq θ n := fun n => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set Kc : ℝ := K0 * (1 + Dq) ^ (2 * Mst) with hKc
  have hKc0 : 0 ≤ Kc := by
    have : 0 ≤ 1 + Dq := by linarith
    positivity
  set E : ℝ := Real.exp (-((Real.pi / 8) ^ 2 / 2) * Dq) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hpern : ∀ n : Fin 2 → ℤ,
      ∑ i : B1WIndex ι h Nw m Ks, ENNReal.ofReal (‖stageMode F θ i n a₁‖ ^ 2) ≤
        ENNReal.ofReal Kc * (ENNReal.ofReal E * ∑ i : B1WIndex ι h Nw m Ks,
          ENNReal.ofReal (((1 + quietYSq θ n) ^ k)⁻¹ * ‖stageMode F θ i n F.a‖ ^ 2) +
          ∑ i : B1WIndex ι h Nw m Ks, if quietYSq θ n < (Real.pi / 8) ^ 2 then
            ENNReal.ofReal (‖stageMode F θ i n F.a‖ ^ 2) else 0) := by
    intro n
    have hw1 : ((1 + quietYSq θ n) ^ k)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [hq0 n]))
    have hw0 : 0 ≤ ((1 + quietYSq θ n) ^ k)⁻¹ :=
      inv_nonneg.2 (pow_nonneg (by linarith [hq0 n]) _)
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    by_cases hbn : (Real.pi / 8) ^ 2 ≤ quietYSq θ n
    · have h1 := pn _ (by positivity) n hbn
      rw [pow_zero, one_mul] at h1
      have hlow : ¬ quietYSq θ n < (Real.pi / 8) ^ 2 := not_lt.2 hbn
      simp only [hlow, ↓reduceIte, Finset.sum_const_zero, add_zero]
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg hw0 (sq_nonneg _),
        ← ENNReal.ofReal_mul hE0, ← ENNReal.ofReal_mul hKc0]
      refine ENNReal.ofReal_le_ofReal (h1.trans (le_of_eq ?_))
      rw [hKc, hE]
      ring
    · have hlow : quietYSq θ n < (Real.pi / 8) ^ 2 := not_le.1 hbn
      have h1 := pn 0 le_rfl n (hq0 n)
      rw [pow_zero, one_mul, zero_div, neg_zero, zero_mul, Real.exp_zero, mul_one] at h1
      simp only [hlow, ↓reduceIte]
      calc ENNReal.ofReal (∑ i : B1WIndex ι h Nw m Ks, ‖stageMode F θ i n a₁‖ ^ 2)
          ≤ ENNReal.ofReal (Kc * ∑ i : B1WIndex ι h Nw m Ks, ‖stageMode F θ i n F.a‖ ^ 2) :=
            ENNReal.ofReal_le_ofReal (h1.trans (mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun i _ => mul_le_of_le_one_left (sq_nonneg _) hw1) hKc0))
        _ = ENNReal.ofReal Kc * ∑ i : B1WIndex ι h Nw m Ks,
              ENNReal.ofReal (‖stageMode F θ i n F.a‖ ^ 2) := by
            rw [ENNReal.ofReal_mul hKc0, ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
        _ ≤ _ := by
            gcongr
            exact le_add_self
  -- the sums over the modes
  have hL' : ∑ i : B1WIndex ι h Nw m Ks, cellNegSq 0 θ (stageScaled F θ i a₁) =
      ∑' n : Fin 2 → ℤ, ∑ i : B1WIndex ι h Nw m Ks,
        ENNReal.ofReal (‖stageMode F θ i n a₁‖ ^ 2) := by
    unfold cellNegSq
    rw [← Summable.tsum_finsetSum fun i _ => ENNReal.summable]
    refine tsum_congr fun n => Finset.sum_congr rfl fun i _ => ?_
    rw [pow_zero, inv_one, one_mul]
    rfl
  have hN : stageDatumNegSq F m Ks k θ = ∑' n : Fin 2 → ℤ, ∑ i : B1WIndex ι h Nw m Ks,
      ENNReal.ofReal (((1 + quietYSq θ n) ^ k)⁻¹ * ‖stageMode F θ i n F.a‖ ^ 2) := by
    unfold stageDatumNegSq cellNegSq
    rw [← Summable.tsum_finsetSum fun i _ => ENNReal.summable]
    refine tsum_congr fun n => Finset.sum_congr rfl fun i _ => ?_
    rw [vecDot_quietFourierFrequency]
    rfl
  have hLow : stageDatumLowSq F m Ks (Real.pi / 8) θ = ∑' n : Fin 2 → ℤ,
      ∑ i : B1WIndex ι h Nw m Ks, if quietYSq θ n < (Real.pi / 8) ^ 2 then
        ENNReal.ofReal (‖stageMode F θ i n F.a‖ ^ 2) else 0 := by
    unfold stageDatumLowSq cellLowSq
    rw [← Summable.tsum_finsetSum fun i _ => ENNReal.summable]
    refine tsum_congr fun n => Finset.sum_congr rfl fun i _ => ?_
    rw [vecDot_quietFourierFrequency]
    rfl
  rw [hL', hN, hLow]
  calc ∑' n : Fin 2 → ℤ, ∑ i : B1WIndex ι h Nw m Ks,
        ENNReal.ofReal (‖stageMode F θ i n a₁‖ ^ 2)
      ≤ ∑' n : Fin 2 → ℤ, ENNReal.ofReal Kc * (ENNReal.ofReal E * ∑ i : B1WIndex ι h Nw m Ks,
          ENNReal.ofReal (((1 + quietYSq θ n) ^ k)⁻¹ * ‖stageMode F θ i n F.a‖ ^ 2) +
          ∑ i : B1WIndex ι h Nw m Ks, if quietYSq θ n < (Real.pi / 8) ^ 2 then
            ENNReal.ofReal (‖stageMode F θ i n F.a‖ ^ 2) else 0) :=
        ENNReal.tsum_le_tsum hpern
    _ = _ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left]

/-- **The quiet entrance quiet margin, proved.** -/
theorem b1_quiet_margin : B1QuietMarginStatement.{u, v} :=
  b1_quiet_margin_of_quietMode (quietModeAssembly stageFamilyZone)
end

/-! # Quiet margin fibre bound: the full-field bound with negative input

`B1NegFullFieldStatement`: at the fibre level, for a start `a₁ ∈ [a, b − 1]`, the terminal stages
are in `H^{K_f}` at the end of the frame, with norm at most `C P_e^Q (1 + (b − a))^Q` times the
`H^{-k}` norms of the stage values at `a₁` (all levels). `a₁ = a`: `stageDatumNegSq`.

`b1_negFullField_of_parts`: the argument (`fullFieldFibre_of_families`) with the plain pass
of negative input from `a₁` (`B1PlainStageNegStatement`). The input of the stage `i` is
`X_i = (C_n N_k(stage_i(a₁)))^{1/2}`, through `b1_pair_le_neg` with the band constants of the
ladder orders (`C_n`, from `TorusHkBandBoundStatement` at `(k, s)`, `s ≤ S_t`). The ladder base is
`sup d + 3 + k ≥ k`, within the reserve `J*(K*(K_f + k))` (`b1_reserve_plain_le`). An infinite
datum makes the right side infinite. The terminal window `[b − 1, b]` lies in `[a₁, b]`.

Constants. As in `fullFieldFibre_of_families`, with the ladder base `sup d + 3 + k`, times `√C_n + 1`:
`C = (√C_b (∑_{k<M} Φ₀ k) C_P + 1)(√C_n + 1)`, `Q = Q_f M + Q_P`.

For zero datum the bound reads `0 ≤ 0`; for `k = 0` it bounds the full field by the `L²` norm
(`N_0` is the `L²` norm).
Constant-order check: `C, Q` after the shape, `K_f` and `k`; before the frame and the frequency. -/

section
open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

universe u v

/-- **The full-field bound with negative input** (the statement). -/
def B1NegFullFieldStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D m Kf k : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    wordReserveJstar (wordReserveKstar (Kf + k) (wordReserveN m Ks) d) d ≤ F.J →
    θ ∈ freqCube → ∀ a₁ : ℝ, F.a ≤ a₁ → a₁ + 1 ≤ F.b →
    stageTerminalBandSq F m Ks Kf 0 θ ≤
      ENNReal.ofReal ((C * peFactor F.η ^ Q * (1 + (F.b - F.a)) ^ Q) ^ 2) *
        ∑ i : B1WIndex ι h Nw m Ks, cellNegSq k θ (stageScaled F θ i a₁)

/-- The ladder with base `sup d + 3 + k` is within the reserve of order `K_f + k`. -/
theorem b1_reserve_plain_le {Nw : ℕ} (Kf k m : ℕ) (d Ks : Fin Nw → ℕ) :
    b1wLadderTop (Finset.univ.sup d + 3 + k) d Ks m + Finset.univ.sup d ≤
      wordReserveJstar (wordReserveKstar (Kf + k) (wordReserveN m Ks) d) d := by
  have hsup : Finset.univ.sup d ≤ ∑ l, d l := Finset.sup_le fun l _ =>
    Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  unfold b1wLadderTop wordReserveJstar wordReserveKstar wordReserveN
  omega

/-- The sources of order `K_f` are within the reserve of order `K_f + k`. -/
theorem b1_reserve_sources_le {Nw : ℕ} (Kf k m : ℕ) (d Ks : Fin Nw → ℕ) :
    wordReserveKstar Kf (wordReserveN m Ks) d + Finset.univ.sup d ≤
      wordReserveJstar (wordReserveKstar (Kf + k) (wordReserveN m Ks) d) d := by
  unfold wordReserveJstar wordReserveKstar
  omega

/-- The constant `√C_n + 1` absorbs `C_n`. -/
theorem b1_neg_arith {s X Cn N : ℝ} (hX : X ^ 2 = Cn * N) (hCn : 0 ≤ Cn) (hN : 0 ≤ N) :
    s ^ 2 * X ^ 2 ≤ (s * (Real.sqrt Cn + 1)) ^ 2 * N := by
  rw [hX, mul_pow]
  have h1 : Cn ≤ (Real.sqrt Cn + 1) ^ 2 := by
    have := Real.sq_sqrt hCn
    nlinarith [Real.sqrt_nonneg Cn]
  have h2 : s ^ 2 * (Cn * N) ≤ s ^ 2 * ((Real.sqrt Cn + 1) ^ 2 * N) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hN) (sq_nonneg _)
  linarith

/-- The squared input of the stages. -/
theorem b1_input_sq {I : Type*} [Fintype I] (Cn : ℝ) (hCn : 0 ≤ Cn) (t : I → ℝ)
    (ht : ∀ i, 0 ≤ t i) :
    Real.sqrt (∑ i, (Real.sqrt Cn * Real.sqrt (t i)) ^ 2) ^ 2 = Cn * ∑ i, t i := by
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, Real.sq_sqrt hCn, Real.sq_sqrt (ht i)]

/-- One constant for the shifted Fourier weights of the orders `k ≤ N ≤ S`. -/
theorem b1_band_uniform (hBand : TorusHkBandBoundStatement) (k S : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N ≤ S, k ≤ N → ∀ (w : TorusHk N ℂ) (θ : Vec 2), θ ∈ freqCube →
      cellBandSq k 0 θ (torusHkValueCLM w : Vec 2 → ℂ) ≤ ENNReal.ofReal (C * ‖w‖ ^ 2) := by
  have hN : ∀ N : Fin (S + 1), ∃ C : ℝ, 0 ≤ C ∧ (k ≤ N.val →
      ∀ (w : TorusHk N.val ℂ) (θ : Vec 2), θ ∈ freqCube →
        cellBandSq k 0 θ (torusHkValueCLM w : Vec 2 → ℂ) ≤ ENNReal.ofReal (C * ‖w‖ ^ 2)) := by
    intro N
    by_cases h : k ≤ N.val
    · obtain ⟨C, hC, hb⟩ := hBand k N.val h
      exact ⟨C, hC, fun _ => hb⟩
    · exact ⟨0, le_rfl, fun h' => absurd h' h⟩
  choose CN hCN hbN using hN
  refine ⟨∑ N, CN N, Finset.sum_nonneg fun N _ => hCN N, fun N hNS hkN w θ hθ => ?_⟩
  refine (hbN ⟨N, Nat.lt_succ_of_le hNS⟩ hkN w θ hθ).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)))
  exact Finset.single_le_sum (f := CN) (fun N _ => hCN N) (Finset.mem_univ _)

/-- The terminal constants on a frame are polynomial in the Péclet factor. -/
theorem b1_termSum_le {Cf Js η Tτ B : ℝ} {Qf Mst : ℕ} (hCf : 0 ≤ Cf) (hJs : 0 ≤ Js)
    (hη : 0 < η) (hTτ : 0 ≤ Tτ) (hB : 0 ≤ B) :
    ∑ k ∈ Finset.range Mst, termConst (Cf * (1 + Js / Real.sqrt η) ^ Qf) Tτ B 1 k ≤
      (∑ k ∈ Finset.range Mst, termConst (Cf * (1 + Js) ^ Qf) Tτ B 1 k) *
        peFactor η ^ (Qf * Mst) := by
  have hP := one_le_peFactor η
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hΛ0 : 0 ≤ Cf * (1 + Js / Real.sqrt η) ^ Qf := by
    have := div_nonneg hJs hs.le
    positivity
  have hΛ₀0 : 0 ≤ Cf * (1 + Js) ^ Qf := by positivity
  have hΛle : Cf * (1 + Js / Real.sqrt η) ^ Qf ≤ Cf * (1 + Js) ^ Qf * peFactor η ^ Qf := by
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (one_add_div_sqrt_le hη hJs) Qf) hCf
  have hPQ : 1 ≤ peFactor η ^ Qf := one_le_pow₀ hP
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  calc termConst (Cf * (1 + Js / Real.sqrt η) ^ Qf) Tτ B 1 k
      ≤ termConst (Cf * (1 + Js) ^ Qf * peFactor η ^ Qf) Tτ B 1 k :=
        termConst_mono hΛ0 hΛle hTτ hB k
    _ ≤ (peFactor η ^ Qf) ^ (k + 1) * termConst (Cf * (1 + Js) ^ Qf) Tτ B 1 k :=
        termConst_le_scale hΛ₀0 hPQ hTτ hB k
    _ ≤ termConst (Cf * (1 + Js) ^ Qf) Tτ B 1 k * peFactor η ^ (Qf * Mst) := by
        rw [← pow_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP
          (Nat.mul_le_mul_left Qf (by omega))) (termConst_nonneg hΛ₀0 hTτ hB k)

/-- The pairing bounds of the stages from their negative norms. -/
theorem b1_neg_input {I : Type*} (st : I → ℕ) (lad : ℕ → ℕ) {k : ℕ} {θ : Vec 2} {Cn : ℝ}
    (hCn : 0 ≤ Cn) (hband : ∀ i : I, ∀ v : TorusHk (lad (st i)) ℂ,
      cellBandSq k 0 θ (torusHkValueCLM v : Vec 2 → ℂ) ≤ ENNReal.ofReal (Cn * ‖v‖ ^ 2))
    (f : I → Vec 2 → ℂ) (hfi : ∀ i, cellNegSq k θ (f i) ≠ ⊤) :
    ∀ (k' : ℕ) (i : I), st i = k' → ∀ w : ComplexCellL2,
      (w : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f i →
      ∀ φ : TorusHk (lad k') ℂ, ‖cellComplexPair w (torusHkValueCLM φ)‖ ≤
        Real.sqrt Cn * Real.sqrt (cellNegSq k θ (f i)).toReal * ‖φ‖ := by
  intro k' i hi w hw φ
  subst hi
  have hneg : cellNegSq k θ (w : Vec 2 → ℂ) = cellNegSq k θ (f i) := by
    unfold cellNegSq
    refine tsum_congr fun n => ?_
    rw [cellCoeff_congr hw n]
  have hpair := b1_pair_le_neg hCn (hband i) w (hneg ▸ hfi i) φ
  rw [hneg] at hpair
  exact hpair

/-- The last step: the terminal band by the inputs. -/
theorem b1_final_le {I : Type*} [Fintype I] {band : ℝ≥0∞} {Bv s X Cn : ℝ} (neg : I → ℝ≥0∞)
    (hfi : ∀ i, neg i ≠ ⊤) (hband : band ≤ ENNReal.ofReal Bv) (hB : Bv ≤ s ^ 2 * X ^ 2)
    (hX : X ^ 2 = Cn * ∑ i, (neg i).toReal) (hCn : 0 ≤ Cn) :
    band ≤ ENNReal.ofReal ((s * (Real.sqrt Cn + 1)) ^ 2) * ∑ i, neg i := by
  have ht0 : ∀ i, 0 ≤ (neg i).toReal := fun i => ENNReal.toReal_nonneg
  have hdatum : ∑ i, neg i = ENNReal.ofReal (∑ i, (neg i).toReal) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => ht0 i]
    exact Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_toReal (hfi i)).symm
  rw [hdatum, ← ENNReal.ofReal_mul (sq_nonneg _)]
  exact hband.trans (ENNReal.ofReal_le_ofReal
    (hB.trans (b1_neg_arith hX hCn (Finset.sum_nonneg fun i _ => ht0 i))))

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The full-field bound with negative input on one frame**, from the plain pass with negative
input from `a₁` (`hplain`), the terminal window as a function of the bound `M` on
`[b − 1, b]` (`hfam`), and the band constants of the output (`C_b`) and of the ladder (`C_n`). -/
theorem b1_negFullField_frame {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (Kf k : ℕ) (d : Fin Nw → ℕ) (a₁ : ℝ) (ha₁ : F.a ≤ a₁) (ha₁b : a₁ + 1 ≤ F.b)
    (CP : ℝ) (QP : ℕ) (hCP : 0 < CP)
    (hplain : ∀ Xn : B1WIndex ι h Nw m Ks → ℝ,
      (∀ (k' : ℕ) (i : B1WIndex ι h Nw m Ks), b1wSt i = k' → ∀ w : ComplexCellL2,
        (w : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] stageScaled F θ i a₁ →
        ∀ φ : TorusHk (b1wLadderAt Nw (Finset.univ.sup d + 3 + k) d Ks k') ℂ,
          ‖cellComplexPair w (torusHkValueCLM φ)‖ ≤ Xn i * ‖φ‖) →
      ∀ t ∈ Icc a₁ F.b, ∀ W : B1WIndex ι h Nw m Ks → ComplexCellL2, IsScaledStage F θ t W →
      ∀ (k' : ℕ) (ψ : B1WIndex ι h Nw m Ks →
        TorusHk (b1wLadderAt Nw (Finset.univ.sup d + 3 + k) d Ks k') ℂ),
        ‖∑ i ∈ stageSet b1wSt k', cellComplexPair (W i) (torusHkValueCLM (ψ i))‖ ≤
          CP * peFactor F.η ^ QP * (1 + (t - a₁)) ^ QP * 1 *
            Real.sqrt (∑ i, Xn i ^ 2) * Real.sqrt (∑ i ∈ stageSet b1wSt k', ‖ψ i‖ ^ 2))
    (Cf Js : ℝ) (Qf Jt St : ℕ) (B : ℝ) (hCf : 0 < Cf) (hJs0 : 0 ≤ Js) (hB : 0 ≤ B)
    (hfam : ∀ Mn : ℝ, 0 ≤ Mn →
      (∀ t ∈ Icc (F.b - 1) F.b, ∀ W : B1WIndex ι h Nw m Ks → ComplexCellL2,
        IsScaledStage F θ t W →
        ∀ (k' : ℕ) (ψ : B1WIndex ι h Nw m Ks →
          TorusHk (b1wLadderAt Nw (Finset.univ.sup d + 3 + k) d Ks k') ℂ),
          ‖∑ i ∈ stageSet b1wSt k', cellComplexPair (W i) (torusHkValueCLM (ψ i))‖ ≤
            Mn * Real.sqrt (∑ i ∈ stageSet b1wSt k', ‖ψ i‖ ^ 2)) →
      ∀ k' < b1wM Nw m Ks, ∃ X : ∀ i : B1WIndex ι h Nw m Ks, TorusHk (b1wPosLadder Kf d i) ℂ,
        (∀ i ∈ stageSet b1wSt k', (torusHkValueCLM (X i) : Vec 2 → ℂ)
          =ᵐ[volume.restrict AVenhance.unitCube] stageScaled F θ i F.b) ∧
        Real.sqrt (∑ i ∈ stageSet b1wSt k', ‖X i‖ ^ 2) ≤
          termConst (Cf * (1 + Js / Real.sqrt F.η) ^ Qf)
            ((((b1wM Nw m Ks : ℕ) : ℝ) + 1) ^ (Jt + St)) B 1 k' * Mn)
    (Cb : ℝ) (hCb0 : 0 ≤ Cb)
    (hband : ∀ i : B1WIndex ι h Nw m Ks, ∀ w : TorusHk (b1wPosLadder Kf d i) ℂ,
      cellBandSq Kf 0 θ (torusHkValueCLM w : Vec 2 → ℂ) ≤ ENNReal.ofReal (Cb * ‖w‖ ^ 2))
    (Cn : ℝ) (hCn0 : 0 ≤ Cn)
    (hbandL : ∀ i : B1WIndex ι h Nw m Ks,
      ∀ v : TorusHk (b1wLadderAt Nw (Finset.univ.sup d + 3 + k) d Ks (b1wSt i)) ℂ,
        cellBandSq k 0 θ (torusHkValueCLM v : Vec 2 → ℂ) ≤ ENNReal.ofReal (Cn * ‖v‖ ^ 2)) :
    stageTerminalBandSq F m Ks Kf 0 θ ≤
      ENNReal.ofReal (((Real.sqrt Cb * (∑ k' ∈ Finset.range (b1wM Nw m Ks),
          termConst (Cf * (1 + Js) ^ Qf) ((((b1wM Nw m Ks : ℕ) : ℝ) + 1) ^ (Jt + St)) B 1 k') *
          CP + 1) * (Real.sqrt Cn + 1) * peFactor F.η ^ (Qf * b1wM Nw m Ks + QP) *
          (1 + (F.b - F.a)) ^ (Qf * b1wM Nw m Ks + QP)) ^ 2) *
        ∑ i : B1WIndex ι h Nw m Ks, cellNegSq k θ (stageScaled F θ i a₁) := by
  classical
  have hab : F.a + 1 ≤ F.b := by linarith only [ha₁, ha₁b]
  have hP := one_le_peFactor F.η
  have hT0 : 0 ≤ F.b - F.a := by linarith only [hab]
  set Mst := b1wM Nw m Ks with hMst
  set Tτ : ℝ := ((Mst : ℝ) + 1) ^ (Jt + St) with hTτ
  have hTτ0 : 0 ≤ Tτ := by positivity
  set S₀ := ∑ k' ∈ Finset.range Mst, termConst (Cf * (1 + Js) ^ Qf) Tτ B 1 k' with hS₀
  have hS₀0 : 0 ≤ S₀ :=
    Finset.sum_nonneg fun k' _ => termConst_nonneg (by positivity) hTτ0 hB k'
  -- an infinite datum
  by_cases hinf : ∑ i : B1WIndex ι h Nw m Ks, cellNegSq k θ (stageScaled F θ i a₁) = ⊤
  · rw [hinf, ENNReal.mul_top (by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have : 0 < (Real.sqrt Cb * S₀ * CP + 1) * (Real.sqrt Cn + 1) := by positivity
      have : 0 < 1 + (F.b - F.a) := by linarith only [hT0]
      positivity)]
    exact le_top
  have hfi : ∀ i : B1WIndex ι h Nw m Ks, cellNegSq k θ (stageScaled F θ i a₁) ≠ ⊤ :=
    fun i => ENNReal.sum_ne_top.1 hinf i (Finset.mem_univ i)
  -- the inputs of the stages
  have hXn := b1_neg_input (I := B1WIndex ι h Nw m Ks) b1wSt
    (b1wLadderAt Nw (Finset.univ.sup d + 3 + k) d Ks) hCn0 hbandL
    (fun i => stageScaled F θ i a₁) hfi
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = Real.sqrt (∑ i : B1WIndex ι h Nw m Ks,
      (Real.sqrt Cn * Real.sqrt (cellNegSq k θ (stageScaled F θ i a₁)).toReal) ^ 2) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; exact Real.sqrt_nonneg _
  set Mn := CP * peFactor F.η ^ QP * (1 + (F.b - F.a)) ^ QP * X with hMn
  have hMn0 : 0 ≤ Mn := by positivity
  -- the plain pass on the terminal window
  have hplain' : ∀ t ∈ Icc (F.b - 1) F.b, ∀ W : B1WIndex ι h Nw m Ks → ComplexCellL2,
      IsScaledStage F θ t W →
      ∀ (k' : ℕ) (ψ : B1WIndex ι h Nw m Ks →
        TorusHk (b1wLadderAt Nw (Finset.univ.sup d + 3 + k) d Ks k') ℂ),
        ‖∑ i ∈ stageSet b1wSt k', cellComplexPair (W i) (torusHkValueCLM (ψ i))‖ ≤
          Mn * Real.sqrt (∑ i ∈ stageSet b1wSt k', ‖ψ i‖ ^ 2) := by
    intro t ht W hW k' ψ
    have ht1 : a₁ ≤ t := (show a₁ ≤ F.b - 1 by linarith only [ha₁b]).trans ht.1
    have ht2 : t ≤ F.b := ht.2
    refine (hplain _ hXn t ⟨ht1, ht2⟩ W hW k' ψ).trans ?_
    have hpow : (1 + (t - a₁)) ^ QP ≤ (1 + (F.b - F.a)) ^ QP :=
      pow_le_pow_left₀ (by linarith only [ht1]) (by linarith only [ht1, ht2, ha₁]) QP
    have hs0 : 0 ≤ Real.sqrt (∑ i ∈ stageSet b1wSt k', ‖ψ i‖ ^ 2) := Real.sqrt_nonneg _
    rw [← hX, mul_one, hMn]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity)) hX0) hs0
  -- the terminal window
  have hfam' := hfam Mn hMn0 hplain'
  set T : ℕ → ℝ := fun k' => termConst (Cf * (1 + Js / Real.sqrt F.η) ^ Qf) Tτ B 1 k'
    with hTdef
  have hs : 0 < Real.sqrt F.η := Real.sqrt_pos.mpr F.piece.hη
  have hΛ0 : 0 ≤ Cf * (1 + Js / Real.sqrt F.η) ^ Qf := by
    have := div_nonneg hJs0 hs.le
    positivity
  have hTk0 : ∀ k', 0 ≤ T k' := fun k' => termConst_nonneg hΛ0 hTτ0 hB k'
  have hterm := terminalBand_le F θ Kf d Cb hCb0 hband T hTk0 Mn hMn0 hfam'
  have hA : ∑ k' ∈ Finset.range Mst, T k' ≤ S₀ * peFactor F.η ^ (Qf * Mst) :=
    b1_termSum_le hCf.le hJs0 F.piece.hη hTτ0 hB
  have harith := fullField_arith (QP := QP) hCb0 hS₀0 hCP.le hP hT0 hX0
    (Finset.sum_nonneg fun k' _ => hTk0 k') hA
  -- the negative datum
  have hXsq : X ^ 2 = Cn * ∑ i : B1WIndex ι h Nw m Ks,
      (cellNegSq k θ (stageScaled F θ i a₁)).toReal := by
    rw [hX]
    exact b1_input_sq Cn hCn0 _ fun i => ENNReal.toReal_nonneg
  refine (b1_final_le (fun i => cellNegSq k θ (stageScaled F θ i a₁)) hfi hterm harith hXsq
    hCn0).trans (le_of_eq ?_)
  refine congrArg (fun x : ℝ => ENNReal.ofReal (x ^ 2) *
    ∑ i : B1WIndex ι h Nw m Ks, cellNegSq k θ (stageScaled F θ i a₁)) ?_
  ring

end Frame

/-- **The full-field bound with negative input**, from the band bound, the family forms of
`CellForcedHsFamilyStatement` and `CellNegativeSmoothingFamilyStatement`, the plain pass with
negative input and `StageSourceHsStatement`. -/
theorem b1_negFullField_of_parts (hBand : TorusHkBandBoundStatement)
    (hP4bF : CellForcedHsFamilyStatement.{u}) (hP4cF : CellNegativeSmoothingFamilyStatement.{u})
    (hPS : B1PlainStageNegStatement.{u, v}) (hP4a : StageSourceHsStatement.{u, v}) :
    B1NegFullFieldStatement.{u, v} := by
  intro K
  obtain ⟨gP, hgP, hPSK⟩ := hPS K
  obtain ⟨gM, hgM, hMK⟩ := amplitudeIdFibresMeas_of_literal.{u, v} amplitudeIdentification
    amplitudeIdForcingCurves K
  refine ⟨min gP gM, lt_min hgP hgM, ?_⟩
  intro Nw D m Kf k d Ks pos
  obtain ⟨CP, QP, hCP, hPSs⟩ := hPSK Nw D m d Ks pos (Finset.univ.sup d + 3 + k) 1
    (Nat.le_add_right _ _) le_rfl
  obtain ⟨B, hB, hP4aK⟩ := hP4a K Nw D m Kf d Ks pos
  obtain ⟨Jt, hJt⟩ : ∃ Jt : ℕ, Jt = Kf + ∑ l, d l + (m + ∑ l, Ks l) := ⟨_, rfl⟩
  obtain ⟨St, hSt⟩ : ∃ St : ℕ, St = b1wLadderTop (Finset.univ.sup d + 3 + k) d Ks m :=
    ⟨_, rfl⟩
  obtain ⟨Cf, Qf, hCf, hwinF⟩ := window_family_uniform.{u} hP4bF hP4cF Jt St
    (ρ := 2 * Real.pi) (by positivity)
  obtain ⟨Cb, hCb0, hbN⟩ := b1_band_uniform hBand Kf Jt
  obtain ⟨Cn, hCn0, hnN⟩ := b1_band_uniform hBand k St
  obtain ⟨Js, hJs⟩ : ∃ Js : ℝ, Js = ∑ l ∈ Finset.range (Jt + St + 2), b1wJets K l := ⟨_, rfl⟩
  have hJs0 : 0 ≤ Js := by
    rw [hJs]
    exact Finset.sum_nonneg fun l _ => le_max_right _ _
  have hS₀0 : 0 ≤ ∑ k' ∈ Finset.range (b1wM Nw m Ks), termConst (Cf * (1 + Js) ^ Qf)
      ((((b1wM Nw m Ks : ℕ) : ℝ) + 1) ^ (Jt + St)) B 1 k' :=
    Finset.sum_nonneg fun k' _ => termConst_nonneg (by positivity) (by positivity) hB k'
  refine ⟨(Real.sqrt Cb * (∑ k' ∈ Finset.range (b1wM Nw m Ks), termConst (Cf * (1 + Js) ^ Qf)
      ((((b1wM Nw m Ks : ℕ) : ℝ) + 1) ^ (Jt + St)) B 1 k') * CP + 1) * (Real.sqrt Cn + 1),
    Qf * b1wM Nw m Ks + QP, by positivity, ?_⟩
  intro ι _ h _ _ _ _ _ _ F θ hlet hJ hθ a₁ ha₁ ha₁b
  have hleP : min gP gM ≤ gP := min_le_left _ _
  have hleM : min gP gM ≤ gM := min_le_right _ _
  obtain ⟨V, hb⟩ := F.piece.hv.2.1
  refine b1_negFullField_frame F θ Kf k d a₁ ha₁ ha₁b CP QP hCP
    (fun Xn hX t ht W hW k' ψ => hPSs (F.mono hleP) θ hlet
      ((b1_reserve_plain_le Kf k m d Ks).trans hJ) hθ V hb (fun _ _ => 1)
      (isFibreKernel_shift (b1wCoeff_eq_real (F.mono hleP) θ).symm
        (plainKernel (F.mono hleP).a (F.mono hleP).b (F.mono hleP).G
          (F.mono hleP).piece.hGm (F.mono hleP).piece.hv V hb θ))
      a₁ ⟨ha₁, show a₁ ≤ F.b by linarith only [ha₁b]⟩ Xn hX t ht W
      ((isScaledStage_mono F hleP θ t W).2 hW) k' ψ)
    Cf Js Qf Jt St B hCf hJs0 hB ?_ Cb hCb0
    (fun i w => hbN _ (hJt ▸ b1wPosLadder_le Kf d i) (b1wPosLadder_ge Kf d i) w θ hθ)
    Cn hCn0
    (fun i v => hnN _ (hSt ▸ b1wLadderAt_le_top (Finset.univ.sup d + 3 + k) m d Ks (b1wSt_lt i))
      ((Nat.le_add_left k _).trans (le_b1wLadderAt Nw _ d Ks _)) v θ hθ)
  intro Mn hMn hpl
  have hfam := fullField_frame_family (F.mono hleM) θ hθ d (Finset.univ.sup d + 3 + k) Kf
    (fun j x e β => hMK (F.mono hleM) j x e θ β) V hb
    (show F.a + 1 ≤ F.b by linarith only [ha₁, ha₁b]) Jt St
    (fun i => hJt ▸ b1wPosLadder_le Kf d i)
    (fun k' hk' => hSt ▸ b1wLadderAt_le_top (Finset.univ.sup d + 3 + k) m d Ks hk') Cf Qf
    hCf.le hwinF Mn hMn hpl B hB
    (hP4aK _ (F.mono hleM) θ hlet ((b1_reserve_sources_le Kf k m d Ks).trans hJ) hθ)
  rw [← hJs] at hfam
  exact hfam
end

end AVRegularity.CycleWords.Seam
end
