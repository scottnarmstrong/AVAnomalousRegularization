-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Assembly.MixedWordsB1Statements
import AVRegularity.CycleWords.Assembly.SeamNorms
import AVRegularity.CycleWords.MixedWords.B1WSourceL2
public import AVRegularity.CycleWords.PlaneBlochEnergyOperator
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

section
section
/-! # The moment amplitudes at fixed frequency (core of `RetainedAmplitudeFactorStatement`)

`RetainedAmplitudeFactorStatement` asks normalized frequency jets of the gauged, cut-off amplitude `e^{-Ξ} χψ ∫ e^{-iθ·y} u`.
Differentiating under the integral, `ϖ^{|β|} ∂_θ^β ∫ e^{-iθ·y} u = ∫ e^{-iθ·y} (-iϖy)^β u`. So, by
Leibniz with the cutoff jets and the jets of `e^{-Ξ}` (`ϖ ∂Ξ = O(x)`, higher normalized jets
`O(1)`, `phaseIntegral_iteratedFDeriv_le`), this reduces to a bound on the **moment amplitudes**
at one frequency (`MomentAmplitudeStatement`). Since `|e^{-Ξ} A| = e^{-Re Ξ}|A|`, this is a bound
on their size by `e^{Re Ξ(b,a,θ)}` times the usual factor and the datum jets without cutoff. The
disc lies in the retained disc `ρ ≤ 2ξ_lo`, slow/fast separated. The
cutoff is restored afterwards by `χ_r^{j+1} ∂^j g = ∑_{i ≤ j} c_{ij} ∂^i(χ_r g)`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

universe u v

/-- The normalized moment amplitude norm of a family at `θ`:
`(∑_x π_x⁻¹ (‖∫ cos(θ·y)(ϖy)^β g_x‖² + ‖∫ sin(θ·y)(ϖy)^β g_x‖²))^{1/2}`. -/
def momentAmpNorm {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) (ϖ : ℝ) (β : ℕ × ℕ) (g : ∀ x, Vec 2 → h x)
    (θ : Vec 2) : ℝ≥0∞ :=
  (∑ x, ENNReal.ofReal ((π x)⁻¹) *
    (ENNReal.ofReal
        (‖∫ y, (Real.cos (vecDot θ y) * (ϖ * y 0) ^ β.1 * (ϖ * y 1) ^ β.2) • g x y‖ ^ 2) +
      ENNReal.ofReal
        (‖∫ y, (Real.sin (vecDot θ y) * (ϖ * y 0) ^ β.1 * (ϖ * y 1) ^ β.2) • g x y‖ ^ 2))) ^
    (1 / 2 : ℝ)

/-- **The moment amplitudes at fixed frequency** (core of `RetainedAmplitudeFactorStatement`;
Lemma 11.11 of the paper at one frequency). On a piece `[a, b]` of duration at most `C_H S` inside a
`CoreScalarPackage` window, ending with a quiet stretch `(b - D_q, b]`, for a chain at descending
slots from compactly supported data (the plane value of `f` vanishes a.e. outside a ball, as in
`RetainedAmplitudeFactorStatement`; `φ` below denotes this datum): at every `θ` of the disc `|ξ| ≤ ρ < ξ₀` and every
`|β| ≤ m`, the normalized moment amplitude of the endpoint is at most `e^{Re Ξ(b,a,θ)}` times
`CΘ_w (1 + x_ξ)^P (1 + P_e^Q(1+S)^Q ((1 + B_p) e^{-c·buffer} + e^{-c D_q}))` times the normalized
Bloch jets of the datum of orders `≤ |β| + ∑K_i`, without cutoff. Each Taylor monomial
`(δy)^γ = η_g^{|γ|}(ϖy)^γ` adds `|γ| ≤ K_i` moments; the gauge enters only through its real part.

For `N_w = 0`, `β = 0` the amplitude of `𝒰f` is `e^{Ξ}⟨ℓ(a), Bφ⟩` up to the terminal
fast pattern, which the row kills and the quiet end damps; `|⟨ℓ, Bφ⟩| ≤ C‖Bφ‖`. For `f = 0` both
sides vanish. For `θ = 0` one has `Ξ = 0` and the `β = 0` amplitude is `∫ u_N(b)`; conservation gives
`∫ u_0(b) = ∫ φ` and every letter is in divergence form, so `∫ u_N(b) = 0` for `N ≥ 1`. In the heat
case `G = I`, `v = 0`, with one letter `div(X₁∇u)` and `K = 1`, the amplitude contains
`δ(b-a)|θ|² e^{-(b-a)|θ|²} ∂_{θ₁}φ̂`, bounded by `(1 + x)^2 e^{Re Ξ} ϖ‖∂_{θ₁} Bφ‖` since
`δ = ϖη_g` and `(b-a)|θ|² ≤ C_H x²`. The constants `P, Q` depend on the orders only, and `C, c`
on `K`, the orders, `C_H` and `ρ`; none depends on `η, S`, the window or the datum. -/
def MomentAmplitudeStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D H m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool), ∃ P Q : ℕ,
  ∀ (CH ρ : ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
    (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
  ∀ (η S ηg t₀ Sw ϖ a b Dq : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (g : ℝ) (reg : BlockRegions) (pkg : CoreScalarPackage K η G v t₀ Sw ϖ reg),
    IsWordPiece K g₁ H J π letters η S ηg ϖ G v g reg a b →
    t₀ ≤ a → a ≤ b → b ≤ t₀ + Sw → b - a ≤ CH * S →
    0 ≤ Dq → Set.Ioc (b - Dq) b ⊆ reg.quiet →
    wordReserveJstar (wordReserveKstar 0 (wordReserveN m Ks) d) d ≤ J →
  ∀ (X₀ : Vec 2) (κ : Fin (Nw + 1) → ι → ℕ), IsWordSlots letters κ →
  ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
    (∃ R : ℝ, ∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → planeValue (f x) z = 0) →
    IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ a b v f (fun _ _ _ => 0) u w →
  ∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) ≤ ρ → ∀ β ∈ momentIndices m,
    momentAmpNorm π ϖ β (fun x => planeValue (u (Fin.last Nw) x b)) θ ≤
      ENNReal.ofReal (Real.exp (blockGauge pkg.actual.lam η a b θ).re *
          (C * wordTheta ηg letters * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ P *
            (1 + peFactor η ^ Q * (1 + S) ^ Q * ((1 + (reg.joins : ℝ)) *
              Real.exp (-c * reg.buffer) + Real.exp (-c * Dq))))) *
        ∑ α ∈ momentIndices (β.1 + β.2 + ∑ i, Ks i),
          ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
            blochFibreDerivNorm π (fun _ => 1) α (fun x => planeValue (f x)) θ

/-- The normalized Bloch jets of the datum up to order `n`, without cutoff:
`∑_{|α| ≤ n} (ϖ^{|α|}/α!) ‖∂^α Bφ(θ)‖`. -/
def datumJets {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) (ϖ : ℝ) (n : ℕ) (φ : ∀ x, Vec 2 → h x)
    (θ : Vec 2) : ℝ≥0∞ :=
  ∑ α ∈ momentIndices n,
    ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
      blochFibreDerivNorm π (fun _ => 1) α φ θ

/-- **The stage inequalities at fixed frequency** (the analysis of the moment amplitudes). The stages
are the pairs (level, moment) in the order of the datum moments they require; `out β` is the top
stage of moment `β`. At each frequency of the disc there are slow coordinates `A_k` (the
normalized pairing with the adjoint solution of the terminal test `1`, gauged by `e^{-Ξ}` and
rescaled by `∏_{i ≤ j} θ_i`) and fast seminorms `B_k` (suprema over transverse tests annihilating
`1 + r`) satisfying the triangular inequalities of `triangularGronwall_majorant_mono`
(majorant form: the fast seminorms need not be measurable). The data `D_k` are
the datum moments the stage requires, `E_k` the replacement and quiet errors, and
`ζ = max(|ξ|, S^{-1/2})` up to a constant. The output relation bounds the moment amplitudes by
`e^{Re Ξ} C Θ_w (A_{out β}(b - a) + B_{out β}(b - a) + E_{out β})` (the terminal amplitude pairs
`W(b)` with `1 = ⟨1 + r(b), 1⟩ ℓ(b) + φ_b`, `φ_b` a fast test).

With no letters and `m = 0` there is one stage, `A_0(t) = |⟨W(a), ℓ̃(a)⟩|` is constant up to the
gauge, `B_0` decays from `‖Bφ‖`, and the output is the transported mean. For `f = 0` all
data vanish and `A = B = 0`. For `θ = 0` one has `ζ = S^{-1/2}`, so `ζ²(b - a) ≤ C_H` with no `x`.
The constants `M`, `out`, `Q` are chosen after the orders, and `C_z, C_d, C_out, Θ, c, c_E` after
`C_H, ρ` and before the data. -/
def WordStageStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D H m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
  ∃ (M : ℕ) (out : ℕ × ℕ → ℕ) (Q : ℕ), (∀ β ∈ momentIndices m, out β < M) ∧
  ∀ (CH ρ : ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo →
  ∃ (Cz Cd Cout Θ c cE : ℝ), 0 ≤ Cz ∧ 0 ≤ Cd ∧ 0 ≤ Cout ∧ 0 ≤ Θ ∧ 0 < c ∧ 0 < cE ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D),
    (∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧ (letters i).positive = pos i) →
  ∀ (η S ηg t₀ Sw ϖ a b Dq : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (g : ℝ) (reg : BlockRegions) (pkg : CoreScalarPackage K η G v t₀ Sw ϖ reg),
    IsWordPiece K g₁ H J π letters η S ηg ϖ G v g reg a b →
    t₀ ≤ a → a ≤ b → b ≤ t₀ + Sw → b - a ≤ CH * S →
    0 ≤ Dq → Set.Ioc (b - Dq) b ⊆ reg.quiet →
    wordReserveJstar (wordReserveKstar 0 (wordReserveN m Ks) d) d ≤ J →
  ∀ (X₀ : Vec 2) (κ : Fin (Nw + 1) → ι → ℕ), IsWordSlots letters κ →
  ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
    (∃ R : ℝ, ∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → planeValue (f x) z = 0) →
    IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ a b v f (fun _ _ _ => 0) u w →
  ∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) ≤ ρ →
  ∃ (A B : ℕ → ℝ → ℝ) (Dd Dp Ec : ℕ → ℝ) (ζ : ℝ),
    0 ≤ ζ ∧ ζ ≤ 1 ∧ ζ ^ 2 * (b - a) ≤ Cz * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ 2 ∧
    Monotone Dd ∧ Monotone Dp ∧ Monotone Ec ∧ (∀ k, 0 ≤ Dd k) ∧ (∀ k, 0 ≤ Dp k) ∧
    (∀ k, ζ * Dp k ≤ Dd k) ∧ (∀ k, 0 ≤ Ec k) ∧
    (∀ k < M, ∀ t ∈ Set.Icc 0 (b - a), ∀ a' b' : ℕ → ℝ → ℝ,
      (∀ k' < k, Continuous (a' k') ∧ Continuous (b' k') ∧
        ∀ r ∈ Set.Icc 0 t, A k' r ≤ a' k' r ∧ B k' r ≤ b' k' r) →
      A k t ≤ Dd k + Ec k + Θ * ∑ k' ∈ Finset.range k,
        ∫ r in (0 : ℝ)..t, (ζ ^ 2 * a' k' r + ζ * b' k' r)) ∧
    (∀ k < M, ∀ t ∈ Set.Icc 0 (b - a), ∀ a' b' : ℕ → ℝ → ℝ,
      (∀ k' < k, Continuous (a' k') ∧ Continuous (b' k') ∧
        ∀ r ∈ Set.Icc 0 t, A k' r ≤ a' k' r ∧ B k' r ≤ b' k' r) →
      B k t ≤ Real.exp (-c * t) * Dp k + Ec k + Θ * ∑ k' ∈ Finset.range k,
        ∫ r in (0 : ℝ)..t, Real.exp (-c * (t - r)) * (ζ * a' k' r + b' k' r)) ∧
    ∀ β ∈ momentIndices m,
      ENNReal.ofReal (Dd (out β)) ≤
        ENNReal.ofReal Cd * datumJets π ϖ (β.1 + β.2 + ∑ i, Ks i) (fun x => planeValue (f x)) θ ∧
      ENNReal.ofReal (Dp (out β)) ≤
        ENNReal.ofReal Cd * datumJets π ϖ (β.1 + β.2 + ∑ i, Ks i) (fun x => planeValue (f x)) θ ∧
      ENNReal.ofReal (Ec (out β)) ≤
        ENNReal.ofReal (Cd * peFactor η ^ Q * (1 + S) ^ Q * ((1 + (reg.joins : ℝ)) *
          Real.exp (-cE * reg.buffer) + Real.exp (-cE * Dq))) *
          datumJets π ϖ (β.1 + β.2 + ∑ i, Ks i) (fun x => planeValue (f x)) θ ∧
      momentAmpNorm π ϖ β (fun x => planeValue (u (Fin.last Nw) x b)) θ ≤
        ENNReal.ofReal (Real.exp (blockGauge pkg.actual.lam η a b θ).re * Cout *
          wordTheta ηg letters * (A (out β) (b - a) + B (out β) (b - a) + Ec (out β)))

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # Elementary facts for the reductions of `cycle_mixed_words`

The moment norm is monotone in its order and satisfies the triangle inequality on measurable
fields; the base slots descend; the retained cutoff vanishes outside `|θ| < π/2`. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

section Moments

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem momentIndices_mono {n n' : ℕ} (hn : n ≤ n') : momentIndices n ⊆ momentIndices n' := by
  intro β hβ
  simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hβ ⊢
  omega

/-- The moment norm is monotone in its order. -/
theorem momentNorm_mono {n n' : ℕ} (hn : n ≤ n') (π : ι → ℝ) (s : ℝ) (F : ∀ v, Vec 2 → h v) :
    momentNorm π n s F ≤ momentNorm π n' s F :=
  Finset.sum_le_sum_of_subset (momentIndices_mono hn)

/-- The triangle inequality of the moment norm. -/
theorem momentNorm_add_le (π : ι → ℝ) (n : ℕ) (s : ℝ) (F G : ∀ v, Vec 2 → h v) :
    momentNorm π n s (fun v z => F v z + G v z) ≤ momentNorm π n s F + momentNorm π n s G := by
  unfold momentNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun β _ => ?_
  rw [← mul_add]
  gcongr
  refine ennreal_weighted_l2_add_le _ _ _ _ fun v => ?_
  simp only [smul_add]
  exact eLpNorm_add_le (by norm_num)

end Moments

/-- The base slots descend along every letter edge. -/
theorem wordBaseSlots_isWordSlots {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D Nw J H : ℕ} {π : ι → ℝ}
    {dom : Set (ℝ × Vec 2)} (letters : Fin Nw → CycleLetter ι h D)
    (hlet : ∀ i, IsCycleLetter π (letters i) dom J H) :
    IsWordSlots letters (wordBaseSlots letters) := by
  intro j x y o hne
  have ho : o.1 ≤ (letters j).order := by
    by_contra hlt
    exact hne ((hlet j).edge_order x y o (Nat.lt_of_not_le hlt))
  have hsplit : (∑ i : Fin Nw, if (j.castSucc : Fin (Nw + 1)).val ≤ i.val then
      (letters i).order else 0) = (letters j).order +
      ∑ i : Fin Nw, if (j.succ : Fin (Nw + 1)).val ≤ i.val then (letters i).order else 0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [Fin.val_castSucc, Fin.val_succ, le_refl, ite_true]
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [Nat.not_succ_le_self, ite_false, zero_add]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    have hv : i.val ≠ j.val := fun hv => hij (Fin.ext hv)
    by_cases hle : j.val ≤ i.val
    · have hle' : j.val + 1 ≤ i.val := by omega
      simp only [hle, hle', ite_true]
    · have hle' : ¬ j.val + 1 ≤ i.val := by omega
      simp only [hle, hle', ite_false]
  show (∑ i : Fin Nw, if (j.succ : Fin (Nw + 1)).val ≤ i.val then (letters i).order else 0) +
      o.1 ≤ (∑ i : Fin Nw, if (j.castSucc : Fin (Nw + 1)).val ≤ i.val then
        (letters i).order else 0) + 2
  rw [hsplit]
  omega

/-- The retained cutoff vanishes outside `|θ| < π/2`. -/
theorem retainedCutoff_eq_zero {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (η : ℝ) {θ : Vec 2} (hθ : Real.pi / 2 ≤ Real.sqrt (vecDot θ θ)) :
    retainedCutoff K η χlo θ = 0 := by
  unfold retainedCutoff
  refine mul_eq_zero_of_right _ (hχ.supp _ ?_)
  have hdot : vecDot ((4 * K.ξlo / Real.pi) • θ) ((4 * K.ξlo / Real.pi) • θ) =
      (4 * K.ξlo / Real.pi) ^ 2 * vecDot θ θ := by
    simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdot, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  by_cases hξ : K.ξlo ≤ 0
  · have : 0 ≤ |4 * K.ξlo / Real.pi| * Real.sqrt (vecDot θ θ) :=
      mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
    linarith
  · replace hξ := lt_of_not_ge hξ
    have hpos : 0 < 4 * K.ξlo / Real.pi := by positivity
    rw [abs_of_pos hpos]
    calc 2 * K.ξlo = 4 * K.ξlo / Real.pi * (Real.pi / 2) := by field_simp; ring
      _ ≤ 4 * K.ξlo / Real.pi * Real.sqrt (vecDot θ θ) := by gcongr

section Block

variable {K : ScalarConstants} {g₁ : ℝ} {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D Nw H J : ℕ} {π : ι → ℝ}
  {letters : Fin Nw → CycleLetter ι h D} {η S ηg t₀ ϖ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2} {g : ℝ} {reg : BlockRegions}

theorem IsWordBlock.ϖ_pos (hB : IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg) :
    0 < ϖ := by
  rw [hB.hϖ]
  exact Real.sqrt_pos.2 (div_pos hB.hη (by linarith [hB.hS]))

theorem IsWordBlock.ϖ_le (hB : IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg) :
    ϖ ≤ Real.sqrt η := by
  rw [hB.hϖ]
  exact Real.sqrt_le_sqrt (div_le_self hB.hη.le hB.hS)

theorem IsWordBlock.wordTheta_nonneg
    (hB : IsWordBlock K g₁ H J π letters η S ηg t₀ ϖ G v g reg) : 0 ≤ wordTheta ηg letters :=
  Finset.prod_nonneg fun i _ => mul_nonneg (hB.hlet i).theta_nonneg
    (by split_ifs <;> linarith [hB.hηg])

end Block

section Zero

/-- Ordered derivatives of the zero function vanish. -/
theorem orderedDerivative_zero_function {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {j : ℕ} (β : DerivativeWord2 j) (z : Vec 2) :
    orderedDerivative β (fun _ : Vec 2 => (0 : E)) z = 0 := by
  rw [orderedDerivative_eq_iteratedFDeriv β (contDiff_const (c := (0 : E))),
    iteratedFDeriv_fun_zero]
  rfl

/-- The weighted jet norm of vanishing jets is zero. -/
theorem weightedJetNorm_of_zero {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ)
    (J : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v) (hJ : ∀ v a w z, J v a w z = 0) :
    weightedJetNorm π p j s r J = 0 := by
  unfold weightedJetNorm
  simp [hJ]

/-- The amplitude jet norm of the zero pair is zero. -/
theorem amplitudeJetNorm_zero {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) (m : ℕ) (ϖ : ℝ)
    (θ : Vec 2) :
    amplitudeJetNorm π m ϖ (fun x (_ : Vec 2) => (0 : h x)) (fun x (_ : Vec 2) => (0 : h x)) θ =
      0 := by
  have h0 : ∀ x (a b : ℕ), thetaPartial a b (fun _ : Vec 2 => (0 : h x)) θ = 0 := by
    intro x a b
    simp [thetaPartial, iteratedFDeriv_fun_zero]
  unfold amplitudeJetNorm
  simp [h0]

/-- The zero function has the zero amplitude pair. -/
theorem isRetainedAmplitude_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℝ) :
    IsRetainedAmplitude (fun _ : Vec 2 => (0 : E)) r (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, integrableOn_zero, integrableOn_zero, fun z => ?_⟩
  simp

end Zero

section Constants

/-- The discard factor is monotone in its constant, power and rate. -/
theorem discardFactor_mono {C₁ C₂ Θ P S B D c₁ c₂ : ℝ} {Q₁ Q₂ : ℕ} (hC₁ : 0 ≤ C₁)
    (hC : C₁ ≤ C₂) (hΘ : 0 ≤ Θ) (hP : 1 ≤ P) (hS : 0 ≤ S) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hQ : Q₁ ≤ Q₂) (hc : c₂ ≤ c₁) :
    C₁ * Θ * P ^ Q₁ * (1 + S) ^ Q₁ * (Real.exp (-c₁ * S) + (1 + B) * Real.exp (-c₁ * D)) ≤
      C₂ * Θ * P ^ Q₂ * (1 + S) ^ Q₂ * (Real.exp (-c₂ * S) + (1 + B) * Real.exp (-c₂ * D)) := by
  have hP0 : 0 ≤ P := by linarith
  have hS1 : 0 ≤ 1 + S := by linarith
  have h1 : P ^ Q₁ ≤ P ^ Q₂ := pow_le_pow_right₀ hP hQ
  have h2 : (1 + S) ^ Q₁ ≤ (1 + S) ^ Q₂ := pow_le_pow_right₀ (by linarith) hQ
  have h3 : Real.exp (-c₁ * S) ≤ Real.exp (-c₂ * S) := Real.exp_le_exp.2 (by nlinarith)
  have h4 : Real.exp (-c₁ * D) ≤ Real.exp (-c₂ * D) := Real.exp_le_exp.2 (by nlinarith)
  have hE1 : 0 ≤ Real.exp (-c₁ * S) + (1 + B) * Real.exp (-c₁ * D) := by positivity
  have hA1 : 0 ≤ C₁ * Θ * P ^ Q₁ * (1 + S) ^ Q₁ := by positivity
  have hA2 : C₁ * Θ * P ^ Q₁ * (1 + S) ^ Q₁ ≤ C₂ * Θ * P ^ Q₂ * (1 + S) ^ Q₂ := by
    have hCΘ : C₁ * Θ ≤ C₂ * Θ := mul_le_mul_of_nonneg_right hC hΘ
    have hC2 : 0 ≤ C₂ * Θ := mul_nonneg (hC₁.trans hC) hΘ
    exact mul_le_mul (mul_le_mul hCΘ h1 (by positivity) hC2) h2 (by positivity)
      (mul_nonneg hC2 (pow_nonneg hP0 _))
  have hE : Real.exp (-c₁ * S) + (1 + B) * Real.exp (-c₁ * D) ≤
      Real.exp (-c₂ * S) + (1 + B) * Real.exp (-c₂ * D) := by
    have : (1 + B) * Real.exp (-c₁ * D) ≤ (1 + B) * Real.exp (-c₂ * D) :=
      mul_le_mul_of_nonneg_left h4 (by linarith)
    linarith
  exact mul_le_mul hA2 hE hE1 (hA1.trans hA2)

/-- Off the well-buffered regime, the full-field factor is dominated by the discard factor. -/
theorem fullField_le_discard {c₁ c C_F C : ℝ} {Q₁ Q_F Q : ℕ} {η S Θ : ℝ} {reg : BlockRegions}
    (hw : ¬IsWellBuffered c₁ Q₁ η S reg) (hCF : 0 ≤ C_F) (hC : C_F ≤ C) (hΘ : 0 ≤ Θ)
    (hS : 0 ≤ S) (hbuf : 0 ≤ reg.buffer) (hQ : Q_F + Q₁ ≤ Q) (hc : c ≤ c₁) :
    C_F * Θ * peFactor η ^ Q_F * (1 + S) ^ Q_F ≤
      C * Θ * peFactor η ^ Q * (1 + S) ^ Q *
        (Real.exp (-c * S) + (1 + reg.joins) * Real.exp (-c * reg.buffer)) := by
  unfold IsWellBuffered at hw
  replace hw := lt_of_not_ge hw
  have hP : 1 ≤ peFactor η := by
    unfold peFactor
    have := inv_nonneg.2 (Real.sqrt_nonneg η)
    linarith
  set P := peFactor η
  set B := (reg.joins : ℝ)
  set D := reg.buffer
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hP0 : 0 ≤ P := by linarith
  have hS1 : 0 ≤ 1 + S := by linarith
  have hbase : 0 ≤ C_F * Θ * P ^ Q_F * (1 + S) ^ Q_F := by positivity
  calc C_F * Θ * P ^ Q_F * (1 + S) ^ Q_F
      ≤ C_F * Θ * P ^ Q_F * (1 + S) ^ Q_F *
          ((1 + B) * P ^ Q₁ * (1 + S) ^ Q₁ * Real.exp (-c₁ * D)) :=
        le_mul_of_one_le_right hbase hw.le
    _ = C_F * Θ * P ^ (Q_F + Q₁) * (1 + S) ^ (Q_F + Q₁) * ((1 + B) * Real.exp (-c₁ * D)) := by
        rw [pow_add, pow_add]
        ring
    _ ≤ C * Θ * P ^ Q * (1 + S) ^ Q * ((1 + B) * Real.exp (-c * D)) := by
        have h1 : P ^ (Q_F + Q₁) ≤ P ^ Q := pow_le_pow_right₀ hP hQ
        have h2 : (1 + S) ^ (Q_F + Q₁) ≤ (1 + S) ^ Q := pow_le_pow_right₀ (by linarith) hQ
        have h3 : Real.exp (-c₁ * D) ≤ Real.exp (-c * D) := Real.exp_le_exp.2 (by nlinarith)
        have hC0 : 0 ≤ C := hCF.trans hC
        have hA : C_F * Θ * P ^ (Q_F + Q₁) * (1 + S) ^ (Q_F + Q₁) ≤ C * Θ * P ^ Q * (1 + S) ^ Q :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hC hΘ) h1 (pow_nonneg hP0 _)
            (mul_nonneg hC0 hΘ)) h2 (pow_nonneg hS1 _)
            (mul_nonneg (mul_nonneg hC0 hΘ) (pow_nonneg hP0 _))
        have hE : (1 + B) * Real.exp (-c₁ * D) ≤ (1 + B) * Real.exp (-c * D) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
        exact mul_le_mul hA hE (by positivity)
          (mul_nonneg (mul_nonneg (mul_nonneg hC0 hΘ) (pow_nonneg hP0 _)) (pow_nonneg hS1 _))
    _ ≤ C * Θ * P ^ Q * (1 + S) ^ Q * (Real.exp (-c * S) + (1 + B) * Real.exp (-c * D)) := by
        have hC0 : 0 ≤ C := hCF.trans hC
        have : 0 ≤ C * Θ * P ^ Q * (1 + S) ^ Q :=
          mul_nonneg (mul_nonneg (mul_nonneg hC0 hΘ) (pow_nonneg hP0 _)) (pow_nonneg hS1 _)
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.exp_pos _).le) this

/-- The discard bound with the constants of an ingredient implies it with larger constants. -/
theorem discard_bound_mono {X M : ℝ≥0∞} {C₁ C₂ Θ P S B D c₁ c₂ : ℝ} {Q₁ Q₂ : ℕ}
    (hX : X ≤ ENNReal.ofReal (C₁ * Θ * P ^ Q₁ * (1 + S) ^ Q₁ *
      (Real.exp (-c₁ * S) + (1 + B) * Real.exp (-c₁ * D))) * M)
    (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C₂) (hΘ : 0 ≤ Θ) (hP : 1 ≤ P) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hD : 0 ≤ D) (hQ : Q₁ ≤ Q₂) (hc : c₂ ≤ c₁) :
    X ≤ ENNReal.ofReal (C₂ * Θ * P ^ Q₂ * (1 + S) ^ Q₂ *
      (Real.exp (-c₂ * S) + (1 + B) * Real.exp (-c₂ * D))) * M :=
  hX.trans (mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal (discardFactor_mono hC₁ hC hΘ hP hS hB hD hQ hc)) zero_le)

/-- Off the well-buffered regime, the full-field bound gives the discard bound. -/
theorem discard_of_fullField {X M : ℝ≥0∞} {c₁ c C_F C : ℝ} {Q₁ Q_F Q : ℕ} {η S Θ : ℝ}
    {reg : BlockRegions}
    (hX : X ≤ ENNReal.ofReal (C_F * Θ * peFactor η ^ Q_F * (1 + S) ^ Q_F) * M)
    (hw : ¬IsWellBuffered c₁ Q₁ η S reg) (hCF : 0 ≤ C_F) (hC : C_F ≤ C) (hΘ : 0 ≤ Θ)
    (hS : 0 ≤ S) (hbuf : 0 ≤ reg.buffer) (hQ : Q_F + Q₁ ≤ Q) (hc : c ≤ c₁) :
    X ≤ ENNReal.ofReal (C * Θ * peFactor η ^ Q * (1 + S) ^ Q *
      (Real.exp (-c * S) + (1 + reg.joins) * Real.exp (-c * reg.buffer))) * M :=
  hX.trans (mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal (fullField_le_discard hw hCF hC hΘ hS hbuf hQ hc)) zero_le)

theorem one_le_peFactor (η : ℝ) : 1 ≤ peFactor η := by
  unfold peFactor
  have := inv_nonneg.2 (Real.sqrt_nonneg η)
  linarith

end Constants

section ZeroMap

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {X : Type*} [AddCommGroup X] [Module ℝ X]

omit [Fintype ι] in
/-- The zero map is smooth and band-limited. -/
theorem zeroMap_band (f : X) (x : ι) (r : ℝ) :
    (∀ M : ℕ, ContDiff ℝ M ((0 : X →ₗ[ℝ] (∀ x, Vec 2 → h x)) f x)) ∧
      HasFourierSupportIn ((0 : X →ₗ[ℝ] (∀ x, Vec 2 → h x)) f x) r :=
  ⟨fun _ => contDiff_const, ⟨_, _, isRetainedAmplitude_zero r⟩⟩

/-- The weighted jets of the zero map vanish. -/
theorem zeroMap_jets (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ) (f : X) (Y : ℝ≥0∞) :
    weightedJetNorm π p j s r
      (fun x _ wd z => orderedDerivative wd ((0 : X →ₗ[ℝ] (∀ x, Vec 2 → h x)) f x) z) ≤ Y := by
  refine le_of_eq_of_le (weightedJetNorm_of_zero π p j s r _ fun x a wd z => ?_) zero_le
  rw [LinearMap.zero_apply, Pi.zero_apply]
  exact orderedDerivative_zero_function wd z

/-- Subtracting the zero map does not change the jets. -/
theorem zeroMap_sub_jets {m Kf : ℕ} (π : ι → ℝ) (s r : ℝ) (f : X)
    (J : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v) :
    jetOutputNorm π m Kf s r (fun x a wd z => J x a wd z -
        orderedDerivative wd ((0 : X →ₗ[ℝ] (∀ x, Vec 2 → h x)) f x) z) =
      jetOutputNorm π m Kf s r J := by
  congr 1
  funext x a wd z
  rw [LinearMap.zero_apply, Pi.zero_apply]
  exact (congrArg (J x a wd z - ·) (orderedDerivative_zero_function wd z)).trans (sub_zero _)

end ZeroMap

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # The future retained kernel of `cycle_seam`

The future complete block contributes `K₊ = 𝒫₊ ∘ P₀`, the
reconstruction of the retained amplitude of the future word applied to the zero cell harmonic of the
entrance datum. Here `𝒫₊` is the retained map of the future block
(`retainedMap`), `P₀` is realized at low frequency by the Fourier cutoff `χ_lo(D/(2√η))`, which is
one on the retained band `|θ| ≤ 2ξ_*√η`, and the composition is extended linearly from the square-
integrable fields to all fields. As for `cycle_mixed_words`, the kernel is the retained map on well-
buffered blocks and `0` on the others, where the seam's fast remainder is paid by the full-field
bound. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

/-- The low pass `θ ↦ χ_lo(θ/(2√η))`. -/
def lowPassCutoff (η : ℝ) (χlo : Vec 2 → ℝ) (θ : Vec 2) : ℝ := χlo ((2 * Real.sqrt η)⁻¹ • θ)

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- On square-integrable functions the literal cutoff is a.e. the `L²` cutoff operator. -/
theorem fourierCutoff_ae_seamCutoffL2 (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    {g : Vec 2 → E} (hg : MemLp g 2 volume) :
    fourierCutoff m g =ᵐ[volume] seamCutoffL2 m R hm hs (hg.toLp g) := by
  have h2 : fourierCutoff m (hg.toLp g) = fourierCutoff m g := by
    funext y
    unfold fourierCutoff
    apply integral_congr_ae
    have ht : (fun x : Vec 2 => (hg.toLp g) (y - x)) =ᵐ[volume] fun x => g (y - x) :=
      ((volume : Measure (Vec 2)).measurePreserving_sub_left y).quasiMeasurePreserving.ae_eq_comp
        hg.coeFn_toLp
    filter_upwards [ht] with x hx
    rw [hx]
  rw [← h2]
  exact (seamCutoffL2_ae m R hm hs _).symm

/-- The literal cutoff is a.e. additive on square-integrable functions. -/
theorem fourierCutoff_add_ae (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    {g₁ g₂ : Vec 2 → E} (h₁ : MemLp g₁ 2 volume) (h₂ : MemLp g₂ 2 volume) :
    fourierCutoff m (fun z => g₁ z + g₂ z) =ᵐ[volume]
      fun z => fourierCutoff m g₁ z + fourierCutoff m g₂ z := by
  have hsum := fourierCutoff_ae_seamCutoffL2 m R hm hs (h₁.add h₂)
  rw [MemLp.toLp_add h₁ h₂, map_add] at hsum
  filter_upwards [hsum, Lp.coeFn_add (seamCutoffL2 m R hm hs (h₁.toLp g₁))
    (seamCutoffL2 m R hm hs (h₂.toLp g₂)), fourierCutoff_ae_seamCutoffL2 m R hm hs h₁,
    fourierCutoff_ae_seamCutoffL2 m R hm hs h₂] with z hz ha h1 h2
  show fourierCutoff m (g₁ + g₂) z = _
  rw [hz, ha, Pi.add_apply, ← h1, ← h2]

/-- The literal cutoff is a.e. homogeneous on square-integrable functions. -/
theorem fourierCutoff_smul_ae (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    (c : ℝ) {g : Vec 2 → E} (hg : MemLp g 2 volume) :
    fourierCutoff m (fun z => c • g z) =ᵐ[volume] fun z => c • fourierCutoff m g z := by
  have hsm := fourierCutoff_ae_seamCutoffL2 m R hm hs (hg.const_smul c)
  rw [MemLp.toLp_const_smul c hg, map_smul] at hsm
  filter_upwards [hsm, Lp.coeFn_smul c (seamCutoffL2 m R hm hs (hg.toLp g)),
    fourierCutoff_ae_seamCutoffL2 m R hm hs hg] with z hz hc h1
  show fourierCutoff m (c • g) z = _
  rw [hz, hc, Pi.smul_apply, ← h1]

end Cutoff

section Kernel

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

variable (ι h) in
/-- The square-integrable fields. -/
def l2Fields : Submodule ℝ (∀ x, Vec 2 → h x) where
  carrier := {g | ∀ x, MemLp (g x) 2 volume}
  add_mem' ha hb x := (ha x).add (hb x)
  zero_mem' _ := MemLp.zero
  smul_mem' c _ hg x := (hg x).const_smul c

end Kernel

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # Assembly of `cycle_mixed_words` from its five statements

Conditional helper: `cycle_mixed_words_of_ingredients` proves the exact statement
of `Providers.cycle_mixed_words` from `RetainedMapExistsStatement`,
`RetainedModelJetsStatement`, `ChainDiscardStatement`, `RetainedGaussianStatement` and
`ChainFullFieldStatement`.

The metric threshold is the least of the five thresholds. On a well-buffered block
(`IsWellBuffered`, at the least rate and the largest power of the three statements that need it)
the witness `P` is the retained plane map `retainedPlaneMap` of the block, a retained map by the
first statement, and the four conjuncts are its band property and the other statements. On the
other blocks `P = 0`: the first, second and fourth conjuncts are trivial, and the full-field bound
pays the discard, whose factor is then at least one (`fullField_le_discard`). -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

universe u v

/-- **`cycle_mixed_words` from its five statements.** -/
theorem cycle_mixed_words_of_ingredients (hE : RetainedMapExistsStatement.{u, v})
    (hM : RetainedModelJetsStatement.{u, v}) (hDis : ChainDiscardStatement.{u, v})
    (hGa : RetainedGaussianStatement.{u, v}) (hFF : ChainFullFieldStatement.{u, v})
    (K : ScalarConstants) :
    ∃ g₁ : ℝ, 0 < g₁ ∧ ∀ (χlo : Vec 2 → ℝ)
    (_hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χlo) (_hχ_even : ∀ ξ, χlo (-ξ) = χlo ξ)
    (_hχ_one : ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ K.ξlo → χlo ξ = 1)
    (_hχ_supp : ∀ ξ, 2 * K.ξlo ≤ Real.sqrt (vecDot ξ ξ) → χlo ξ = 0)
    (Nw D H Kf m : ℕ) (_hD : 2 ≤ D)
    (Cout : ℝ) (_hCout : 0 < Cout) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool),
    ∃ (C c CGa cGa : ℝ) (Q : ℕ) (CM : ℕ → ℝ), 0 < C ∧ 0 < c ∧ 0 < CGa ∧ 0 < cGa ∧
      (∀ M, 0 < CM M) ∧
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ x, 0 < π x)
        (letters : Fin Nw → CycleLetter ι h D)
        (_hletters : ∀ i, (letters i).order = d i ∧ (letters i).slow = Ks i ∧
          (letters i).positive = pos i)
        (η S ηg rstar t₀ ϖ : ℝ) (_hη : 0 < η) (_hη1 : η ≤ 1) (_hS : 1 ≤ S) (_hηg : 0 < ηg)
        (_hηg1 : ηg ≤ 1) (_hrstar : 0 < rstar) (_hrstarC : rstar ≤ Cout)
        (_hϖ : ϖ = Real.sqrt (η / S))
        (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
        (_hGm : IsCellMetric (fun t _ => G t)) (_hv : IsCellDrift v)
        (_hv0 : ∀ t (k : Fin 2), cellMean (fun x => (v t x k : ℂ)) = 0)
        (_hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
        (_hvw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
        (_hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj j)
        (_hg0 : 0 ≤ g) (_hg : g ≤ K.g0) (_hg₁ : g ≤ g₁)
        (_hGn : IsMetricNearIdentity (fun t _ => G t) g)
        (reg : BlockRegions) (_pkg : ScalarPackage K η G v t₀ S ϖ reg)
        (_hlet : ∀ i, IsCycleLetter π (letters i) (Set.Icc t₀ (t₀ + S) ×ˢ Set.univ)
          (wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d) H)
        (_htrans : ∀ i, IsTransverseOnPulses (letters i).edge
          (fun p : Fin reg.P => Set.Icc (reg.lo p) (reg.hi p)) reg.orient)
        (_hquiet : ∀ i, IsQuietOn (letters i).edge v reg.quiet)
        (_hmeas : ∀ i x y o, ∀ γ ∈ (letters i).edge x y o, ∀ α X z,
          Measurable fun t => γ.coeff α t X z)
        (X₀ : Vec 2) (κ : Fin (Nw + 1) → ι → ℕ) (_hκf : ∀ x, Kf ≤ κ (Fin.last Nw) x)
        (_hκ : ∀ (j : Fin Nw) x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
          κ j.succ x + o.1 ≤ κ j.castSucc y + 2),
      ∃ P : (∀ x, PlaneHk Set.univ (κ 0 x) (h x)) →ₗ[ℝ] (∀ x, Vec 2 → h x),
        (∀ f x, (∀ M : ℕ, ContDiff ℝ M (P f x)) ∧
          HasFourierSupportIn (P f x) (2 * K.ξlo * Real.sqrt η)) ∧
        (∀ (M : ℕ) (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)),
          momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) < ⊤ →
          weightedJetNorm π (m : ℝ) M ϖ ϖ⁻¹
              (fun x _a wd z => orderedDerivative wd (P f x) z) ≤
            ENNReal.ofReal (CM M * wordTheta ηg letters) *
              momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x))) ∧
        (∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
          (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
          (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
          momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x)) < ⊤ →
          IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f
            (fun _j _x _ => 0) u w →
          jetOutputNorm π m Kf ϖ rstar
              (fun x a wd z => planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
                orderedDerivative wd (P f x) z) ≤
            ENNReal.ofReal (C * wordTheta ηg letters * peFactor η ^ Q * (1 + S) ^ Q *
                (Real.exp (-c * S) + (1 + reg.joins) * Real.exp (-c * reg.buffer))) *
              momentNorm π (wordReserveN m Ks) ϖ (fun x => planeValue (f x))) ∧
        (∀ f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x),
          momentNorm π (wordReserveN m Ks + 2) ϖ (fun x => planeValue (f x)) < ⊤ →
          ∃ A B : ∀ x, Vec 2 → h x,
            (∀ x, IsRetainedAmplitude (P f x) (2 * K.ξlo * Real.sqrt η) (A x) (B x)) ∧
            (∀ x, ContDiff ℝ m (A x) ∧ ContDiff ℝ m (B x)) ∧
            (∀ x θ, A x (-θ) = A x θ ∧ B x (-θ) = -B x θ) ∧
            ∀ θ : Vec 2, (∀ i, |θ i| ≤ Real.pi) →
              amplitudeJetNorm π m ϖ A B θ ≤
                ENNReal.ofReal (CGa * wordTheta ηg letters *
                    (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ wordReserveP m Ks *
                    Real.exp (-cGa * (vecDot θ θ / ϖ ^ 2))) *
                  ∑ α ∈ momentIndices (wordReserveN m Ks),
                    ENNReal.ofReal (ϖ ^ (α.1 + α.2) /
                        ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
                      blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α
                        (fun x => planeValue (f x)) θ) := by
  have hE0 := (hE K).choose_spec
  have hM0 := (hM K).choose_spec
  have hD0 := (hDis K).choose_spec
  have hG0 := (hGa K).choose_spec
  have hF0 := (hFF K).choose_spec
  refine ⟨min (min (hE K).choose (hM K).choose)
      (min (min (hDis K).choose (hGa K).choose) (hFF K).choose),
    lt_min (lt_min hE0.1 hM0.1) (lt_min (lt_min hD0.1 hG0.1) hF0.1), ?_⟩
  intro χlo hχ_smooth hχ_even hχ_one hχ_supp Nw D H Kf m hD Cout hCout d Ks pos
  have hχ : IsLowCutoff K χlo := ⟨hχ_smooth, hχ_even, hχ_one, hχ_supp⟩
  -- the retained map is built with `χ_lo^{n+1}`
  have hχ' := hχ.pow (wordReserveN m Ks)
  have hE1 := hE0.2 _ hχ' Nw D H d Ks pos
  have hM1 := hM0.2 _ hχ' Nw D H m d Ks pos
  have hD1 := hD0.2 _ hχ' Nw D H Kf m Cout hCout d Ks pos
  have hG1 := hG0.2 χlo hχ Nw D H m d Ks pos
  have hF1 := hF0.2 Nw D H Kf m Cout hCout d Ks pos
  have hEs := hE1.choose_spec.choose_spec
  have hMs := hM1.choose_spec.choose_spec.choose_spec
  have hDs := hD1.choose_spec.choose_spec.choose_spec
  have hGs := hG1.choose_spec.choose_spec.choose_spec.choose_spec
  have hFs := hF1.choose_spec.choose_spec
  refine ⟨hD1.choose + hF1.choose,
    min hD1.choose_spec.choose
      (min (min hE1.choose hM1.choose_spec.choose) hG1.choose_spec.choose_spec.choose),
    hG1.choose, hG1.choose_spec.choose,
    max hD1.choose_spec.choose_spec.choose (hF1.choose_spec.choose +
      max (max hE1.choose_spec.choose hM1.choose_spec.choose_spec.choose)
        hG1.choose_spec.choose_spec.choose_spec.choose),
    hM1.choose, add_pos hDs.1 hFs.1,
    lt_min hDs.2.1 (lt_min (lt_min hEs.1 hMs.2.1) hGs.2.2.1), hGs.1, hGs.2.1, hMs.1, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ letters hletters η S ηg rstar t₀ ϖ hη hη1 hS hηg hηg1 hrstar
    hrstarC hϖ G v g hGm hv hv0 hvs hvw hvj hg0 hg hg₁ hGn reg pkg hlet htrans hquiet hmeas X₀ κ
    hκf hκ
  have hB : IsWordBlock K _ H (wordReserveJstar (wordReserveKstar Kf (wordReserveN m Ks) d) d)
      π letters η S ηg t₀ ϖ G v g reg :=
    ⟨hD, hπ, hη, hη1, hS, hηg, hηg1, hϖ, hGm, hv, hv0, hvs, hvw, hvj, hg0, hg, hg₁, hGn, hlet,
      htrans, hquiet, hmeas⟩
  have hJ0 := wordReserveJstar_le 0 Kf 0 m Ks d (Nat.zero_le _) (Nat.zero_le _)
  have hJm := wordReserveJstar_le 0 Kf m m Ks d (Nat.zero_le _) le_rfl
  have hmeas' : ∀ f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x), ∀ x,
      AEStronglyMeasurable (planeValue (f x)) volume := fun f x =>
    (planeJetOrder_memLp (Nat.zero_le _) (f x) _).aestronglyMeasurable
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hbuf : 0 ≤ reg.buffer := pkg.buffer_nonneg
  have hΘ := hB.wordTheta_nonneg
  by_cases hwb : IsWellBuffered
      (min (min hE1.choose hM1.choose_spec.choose) hG1.choose_spec.choose_spec.choose)
      (max (max hE1.choose_spec.choose hM1.choose_spec.choose_spec.choose)
        hG1.choose_spec.choose_spec.choose_spec.choose) η S reg
  · have hR := retainedMap_spec (hEs.2 _ π letters hletters η S ηg t₀ ϖ G v g reg pkg
      (hB.mono ((min_le_left _ _).trans (min_le_left _ _))) hJ0
      (hwb.mono ((min_le_left _ _).trans (min_le_left _ _))
        ((le_max_left _ _).trans (le_max_left _ _)) hS0 hbuf) X₀)
    exact ⟨retainedPlaneMap K (fun ξ => χlo ξ ^ (wordReserveN m Ks + 1)) π letters η S ηg t₀ ϖ G v
      X₀ (κ 0), fun f x => hR.band _ x,
      fun M f hf => hMs.2.2 _ π letters hletters η S ηg t₀ ϖ G v g reg pkg
        (hB.mono ((min_le_left _ _).trans (min_le_right _ _))) hJm
        (hwb.mono ((min_le_left _ _).trans (min_le_right _ _))
          ((le_max_right _ _).trans (le_max_left _ _)) hS0 hbuf) X₀ _ hR M _ (hmeas' f) hf,
      fun f u w hf hch => discard_bound_mono
        (hDs.2.2 _ π letters hletters η S ηg rstar t₀ ϖ G v g reg pkg
          (hB.mono ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))))
          le_rfl hrstar hrstarC X₀ _ hR κ hκf hκ f u w hf hch)
        hDs.1.le (le_add_of_nonneg_right hFs.1.le) hΘ (AVRegularity.CycleWords.Assembly.one_le_peFactor η) hS0
        (Nat.cast_nonneg _) hbuf (le_max_left _ _) (min_le_left _ _),
      fun f hf => hGs.2.2.2 _ π letters hletters η S ηg t₀ ϖ G v g reg pkg
        (hB.mono ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))))
        hJm (hwb.mono (min_le_right _ _) (le_max_right _ _) hS0 hbuf) X₀ _ hR _ (hmeas' f) hf⟩
  · exact ⟨0, fun f x => zeroMap_band f x _, fun M f _ => zeroMap_jets π _ _ _ _ f _,
      fun f u w hf hch => le_of_eq_of_le (zeroMap_sub_jets π ϖ rstar f _)
        (discard_of_fullField
          (hFs.2 _ π letters hletters η S ηg rstar t₀ ϖ G v g reg pkg
            (hB.mono ((min_le_right _ _).trans (min_le_right _ _))) le_rfl hrstar hrstarC X₀ κ
            hκf hκ f u w hf hch)
          hwb hFs.1.le (le_add_of_nonneg_left hDs.1.le) hΘ hS0 hbuf (le_max_right _ _)
          (min_le_right _ _)),
      fun f _ => ⟨fun _ _ => 0, fun _ _ => 0, fun x => isRetainedAmplitude_zero _,
        fun x => ⟨contDiff_const, contDiff_const⟩, fun x θ => ⟨rfl, neg_zero.symm⟩,
        fun θ _ => le_of_eq_of_le (amplitudeJetNorm_zero π m ϖ θ) zero_le⟩⟩

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # The crude pass of the word fibre facts: polynomial regularity of the cell equation with a smooth drift (statement)

For the homogeneous cell equation `u' = D_θ·(G D_θ u) - v·D_θ u` with a constant-in-space metric, a
real shift `|θ| ≤ ρ` and a smooth divergence-free drift whose jets of order `≤ j + 1` are at most
`L`, the `H^j` theory has constants polynomial in `1 + L`:

* (G) growth on unit windows: `‖u(t)‖_{H^j} ≤ C(1+L)^Q‖u(a)‖_{H^j}` for `t ≤ a + 1`;
* (S) smoothing after unit time: `‖u(t)‖_{H^j} ≤ C(1+L)^Q‖u(a)‖_{L²}` for `a + 1 ≤ t ≤ a + 2`.

The transport does no work in the top-order energy (incompressibility); its commutators cost `L`.
The polynomial price comes from using short smoothing only on ends of length `c/(1+L)` and the
`L²` contraction in the middle. The word fibre facts use it
with `L = J/√η ≤ J·P_e` for the crude pass (crude H3/H4 with `ν = H^{s_k}`) and for the
leakage of discarded crossings. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleWords.Assembly

/-- **Polynomial regularity of the cell equation with a smooth drift**.

For `v = 0` (in particular `L = 0`) this is the twisted heat equation, an `H^j` contraction with
smoothing. For `j = 0`, (G) and (S) are the `L²` contraction of a real shift with a divergence-free
drift (`cellDualDerivative_real_energy`). For large `L`, on `[a, a + c/(1+L)]` the order-`j` energy
grows by `e^{C L t} ≤ e^{Cc}`; after it, the `L²` contraction and a smoothing end of length
`c/(1+L)` cost `(1+L)^{j/2}`. The constants `C, Q` are chosen after `j, ρ` and before the window,
the metric, the drift, `L` and the data. -/
def CellDriftRegularityStatement : Prop :=
  ∀ (j : ℕ) (ρ : ℝ), 0 ≤ ρ → ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
  ∀ (a b L : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2),
    a ≤ b → 0 ≤ L → Real.sqrt (vecDot θ θ) ≤ ρ →
    (∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    (∀ (l : ℕ) t, l ≤ j + 1 → t ∈ Set.Icc a b → ∀ x, ‖iteratedFDeriv ℝ l (v t) x‖ ≤ L) →
  ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
    CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t
        (slice t) 0 0) →
    (∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u a → ∀ t ∈ Set.Icc a b, t ≤ a + 1 →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = u t ∧ ‖w‖ ≤ C * (1 + L) ^ Q * ‖w₀‖) ∧
    (∀ t ∈ Set.Icc a b, a + 1 ≤ t → t ≤ a + 2 →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = u t ∧ ‖w‖ ≤ C * (1 + L) ^ Q * ‖u a‖)

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # Local transversality in H^j: smallness-free regularity of the reduced transverse equation

On transverse functions (constant along `e_∥`) the cell equation of a shear drift
`v = V(t, z_⊥) e_∥` loses its transport `V ∂_∥` and becomes the reduced scalar-multiplier equation
`u' = D_θ·(G D_θ u) - i (√η ξ·v) u` (`cellScalarMultiplierDual`;
`cellTransverse_actual_reduced_weak_curve` passes from the full equation to the reduced one).
The potential `√η ξ·v` has jets `|ξ| J_l` with `J_l` bounds of the normalized drift jets, so its
regularity theory is `P_e`-free. `TransverseRegularityStatement` is that theory with no smallness
of `|ξ|` relative to `C_w` or `J` (only `|ξ| ≤ ρ`): constants depending on `j, ρ, C_w, J`.

* (G) growth on unit windows: `‖u(t)‖_{H^j} ≤ C‖u(a)‖_{H^j}` for `t ≤ a + 1`;
* (S) smoothing after unit time: `‖u(t)‖_{H^j} ≤ C‖u(a)‖_{L²}` for `a + 1 ≤ t ≤ a + 2`;
* (C1) the solution from the constant `1`: `‖u(t) - 1‖_{H^j} ≤ C|ξ|` for `t ≤ a + 2`.

Decay at the `L²` rate, the row and the graph follow in the adapters (local transversality). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleWords.Assembly

/-- **Smallness-free regularity of the reduced transverse equation** (local transversality, H^j
layer).

For `v = 0` this is the twisted heat equation, a contraction in every `H^j`, smoothing, and
`u(t) = e^{-∫θGθ}·1` from `1`, with `|1 - e^{-∫θGθ}| ≤ 4|θ|² ≤ 4ρ|ξ|` for `t ≤ a + 2`
(`|θ| = √η|ξ| ≤ |ξ| ≤ ρ`). For `ξ = 0` there is no shift and no potential, and `u ≡ 1` from `1`. For
`j = 0`, (G) and (S) are the `L²` growth bound on unit windows, and (C1) is the `L²` Duhamel bound
of the forcing `-i(√ηξ·v)·1 - θGθ·1 = O(|ξ|)`. The constant `C` is chosen after `j, ρ, C_w, J` and
before the window, the metric, the drift and the data. -/
def TransverseRegularityStatement : Prop :=
  ∀ (j : ℕ) (ρ Cw : ℝ) (J : ℕ → ℝ), 0 ≤ ρ → 0 ≤ Cw → (∀ l, 0 ≤ J l) →
  ∃ C : ℝ, 0 < C ∧
  ∀ (a b η : ℝ) (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (ξ : Fin 2 → ℂ),
    a ≤ b → 0 ≤ η → η ≤ 1 → (∀ i, (ξ i).im = 0) → fibreNorm ξ ≤ ρ →
    (∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    (∀ (l : ℕ) t, t ∈ Set.Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • v t x) x‖ ≤ J l) →
  ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
    CellWeakHilbertCurve a b u slice
      (fun t => cellScalarMultiplierDual η Cw hCw G hG hv hw ξ 0 t (slice t)) →
    (∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u a → ∀ t ∈ Set.Icc a b, t ≤ a + 1 →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = u t ∧ ‖w‖ ≤ C * ‖w₀‖) ∧
    (∀ t ∈ Set.Icc a b, a + 1 ≤ t → t ≤ a + 2 →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = u t ∧ ‖w‖ ≤ C * ‖u a‖) ∧
    (u a = cellConstantCLM 1 → ∀ t ∈ Set.Icc a b, t ≤ a + 2 →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = u t - cellConstantCLM 1 ∧
        ‖w‖ ≤ C * fibreNorm ξ)

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # The fibre-level inputs of the retained amplitude, and the adjoint chain

The proof of `RetainedAmplitudeFactorStatement` runs on
the Bloch fibres of the word chain. Its fibre-level inputs:

* `AmplitudeIdentificationStatement`: the Bloch periodic parts of the chain levels form a chain
  of fibre solutions forced by the Bloch transforms of the letter fluxes, and the Fourier amplitude
  of the endpoint is the cell integral of the last one (proof: the one-level Duhamel identities
  `wordChainSuccessor_l2_duhamel` against backward Bloch fields, i.e. the adjoint chain, and
  `AdjointFibreStatement`).
* Local transversality: on an orientation region the local (single-orientation)
  graph, row and adjoint fast propagator are transverse, with `P_e`-free jets up to the buffer
  error `P_e^Q e^{-c D_q}` (on transverse functions the shear transport vanishes).
* Transverse blocks: the four blocks `LCR`, `LCQ`, `QCR`, `QCQ` of a frozen
  constituent: the outer derivative gives one zero on the
  tested row, the positive derivative on the column the other.
* Quiet replacement: replacement of the actual fast part by the local one on a
  region, and the quiet-region identities with sources.

The Taylor monomials of a letter act on Bloch periodic parts as frequency derivatives,
`planeBlochC θ (y^β g) = (i∂_θ)^β planeBlochC θ g`; this elementary identity is proved with the
assembly of `RetainedAmplitudeFactorStatement`, together with the excursion count.

The adjoint chain:

* `AdjointFibreStatement`: the Bloch fibres of the reversed adjoint chain are fibre solutions
  of the reversed problem, in the form used by `adjoint_decay` and `adjoint_smoothing`.
* Weighted short smoothing of the homogeneous forward plane chain from a negative order into
  positive jets.

Conventions: the fibre shift is `θ = √η ξ`; in the radian convention used here the plane frequency
`θ` has fibre frequency `planeFibreFrequency η θ = θ/√η`; the library Bloch transform
`planeCellBlochTransform` uses `planePhysicalFibreFrequency η θ = 2πθ/√η`. Pairings are
bilinear, so the forward fibre at `θ` pairs with the adjoint fibre at `-θ`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

universe u v

/-! ## Fibre calculus -/

/-- The covariant derivative `∂_k + iθ_k` at the fibre shift `θ = √η ξ`. -/
def fibreCovDeriv (θ : Vec 2) (k : Fin 2) (g : Vec 2 → ℂ) : Vec 2 → ℂ :=
  fun z => fderiv ℝ g z (basisVec k) + Complex.I * (θ k : ℂ) * g z

/-- The Bloch periodic part `∑_k e^{-iθ·(z+k)} g(z+k)` of a plane function (radian convention). Its
cell integral is the Fourier transform `∫ e^{-iθ·y} g(y) dy` when `g` is integrable, and it carries
the derivative `∂_k` of `g` to `∂_k + iθ_k`: the fibre shift is `θ`. -/
def planeBlochC (θ : Vec 2) (g : Vec 2 → ℝ) (z : Vec 2) : ℂ :=
  ∑' k : Fin 2 → ℤ, Complex.exp (-(Complex.I * (vecDot θ (z + fun i => (k i : ℝ)) : ℂ))) *
    (g (z + fun i => (k i : ℝ)) : ℂ)

/-- The monomial weight `y^β`. -/
def momentWeight (β : ℕ × ℕ) (y : Vec 2) : ℝ := y 0 ^ β.1 * y 1 ^ β.2

/-- The gradient of `y^β`. -/
def momentWeightGrad (β : ℕ × ℕ) (y : Vec 2) : Fin 2 → ℝ :=
  ![(β.1 : ℝ) * y 0 ^ (β.1 - 1) * y 1 ^ β.2, (β.2 : ℝ) * y 0 ^ β.1 * y 1 ^ (β.2 - 1)]

/-- `tr(G ∇² y^β)`. -/
def momentWeightLap (G : Matrix (Fin 2) (Fin 2) ℝ) (β : ℕ × ℕ) (y : Vec 2) : ℝ :=
  G 0 0 * ((β.1 : ℝ) * ((β.1 : ℝ) - 1) * y 0 ^ (β.1 - 2) * y 1 ^ β.2) +
    (G 0 1 + G 1 0) * ((β.1 : ℝ) * (β.2 : ℝ) * y 0 ^ (β.1 - 1) * y 1 ^ (β.2 - 1)) +
    G 1 1 * ((β.2 : ℝ) * ((β.2 : ℝ) - 1) * y 0 ^ β.1 * y 1 ^ (β.2 - 2))

/-! ## The adjoint chain -/

/-- **The Bloch fibres of the reversed adjoint chain.**
A reversed homogeneous plane chain (metric `G(-·)`, drift `-v(-·)`, on `[-b, -a]`, as produced by
`exists_reversedAdjoint`) has Bloch fibres that are cell solutions of the reversed fibre problem at
the library frequency `planePhysicalFibreFrequency η θ`, for every time and almost every `θ` of the
centred cell. With `ξ = -planePhysicalFibreFrequency η θ` these are the adjoint solutions of
`FibreScalarData.adjoint_decay` and `adjoint_smoothing`; they pair with the forward fibre at `-θ`.
(Route: `backwardField_trace_eq_reversedChain` identifies the chain with the Bloch synthesis of the
reversed fibre solutions; their Bloch transform is that family.)

For a zero datum the chain is `0` and `Ψ = 0` solves. For `a = b` the interval is a point and
the identity is the Bloch transform of the datum. For `v = 0`, `G = I` the fibres are the heat
multipliers `e^{-(τ+b)|2πk + 2πθ|²}` on the Fourier coefficients of the datum's fibre. As for signs,
`planePhysicalFibreFrequency η (-θ) = -planePhysicalFibreFrequency η θ`, so `Ψ θ` is admissible for
`adjoint_decay` at the frequency of the forward fibre at `-θ`. There are no constants;
the slot `m` only enters through `planeHkValueOperator m`. -/
def AdjointFibreStatement : Prop :=
  ∀ (a b : ℝ), a ≤ b → ∀ η : ℝ, 0 < η →
  ∀ G : ℝ → Matrix (Fin 2) (Fin 2) ℝ, IsCellMetric (fun t _ => G t) →
  ∀ v : ℝ → Vec 2 → Vec 2, IsCellDrift v → ∀ V : ℝ, (∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) →
  ∀ (m : ℕ) (gd : ∀ _ : Unit, PlaneHk Set.univ m ℝ)
    (ψ : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ),
    IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-b) (-a)
      (fun τ z => -(v (-τ) z)) gd (fun _ _ _ => 0) ψ ψw →
  ∃ Ψ : Vec 2 → ℝ → RawJet2 1 ℂ,
    (∀ θ, IsCellSolution (Set.Icc (-b) (-a))
      (fibreCoefficients η (fun τ => G (-τ)) (fun τ z => -(v (-τ) z))
        (planePhysicalFibreFrequency η θ) (fun _ => 0))
      (fun _ _ => 0) (fun _ _ => 0) (Ψ θ)) ∧
    ∀ τ ∈ Set.Icc (-b) (-a), ∀ᵐ θ ∂centeredPlaneFrequencyMeasure,
      cellValue (Ψ θ) τ =ᵐ[volume.restrict AVenhance.unitCube]
        ⇑(planeCellBlochTransform centeredPlaneFrequencyBase 1 one_pos
          (ofRealL2 volume (planeHkValueOperator m (ψ 0 () τ))) θ)

/-! ## Transverse blocks -/

/-! ## Buffered replacement and quiet means -/

/-! ## The amplitude identification -/

/-- **The amplitude identification** (the word identities). For a word chain on a piece from
smooth compactly supported data:
every level has all moments in `L¹`; for every component, every vector `e` of its Hilbert space,
every plane frequency `θ` and every moment `β`, the Bloch periodic part of `⟨e, y^β u_j(t)⟩` is (the
value of) a cell solution of the actual fibre problem at `planeFibreFrequency η θ`. With
`m = y^β` and `Φ` the previous-level letter flux `wordChainPreviousFlux` (`0` at level `0`),
`∂_t(mu) = L(mu) + div(mΦ - u(G+Gᵀ)∇m) + (tr(G∇²m) + v·∇m)u - ∇m·Φ`. So the flux is the Bloch
periodic part of `⟨e, mΦ - u(G+Gᵀ)∇m⟩` and the scalar source that of `⟨e, (tr(G∇²m) + v·∇m)u -
∇m·Φ⟩`; for `β = 0` the flux is the letter flux and the source is `0`. The moments make the
frequency jets of the amplitude, and the Taylor monomials of the letters, fibre quantities at one
frequency (the moment amplitudes statement `MomentAmplitudeStatement`). And the
Fourier transform of `⟨e, u_N(b)⟩` at `θ` is the cell integral of its Bloch periodic part. The
retained amplitudes are `(2π)⁻²` times the cutoff times this. (Route: the one-level identities
`wordChainSuccessor_l2_duhamel`, tested against backward Bloch fields, i.e.
`AdjointFibreStatement`; uniqueness of fibre
solutions; finite moments from compact data: the plane value of `f` vanishes a.e. outside a
ball, as in `RetainedAmplitudeFactorStatement`.)

At level `0` with `β = 0` the flux is `0` (`wordChainPreviousFlux_initial`), and the
statement is the forced-free Bloch identification (`scalarRealPlaneChain_blochValue`) at the radian
frequency. For `β = e₁`, `G = I`, `v = 0` at level `0`, `∂_t(y₁u) = Δ(y₁u) - 2∂₁u`, i.e. the flux is
`-2u e₁` and the source is `0` (`[Δ, y₁] = 2∂₁`). Here `momentWeight (0,0) = 1`, and its gradient and
`momentWeightLap` vanish (the factors `β.i` are `0`).
For `N = 0` there are no letters and the amplitude is that of `𝒰f`. For `θ = 0` the Bloch periodic
part is the periodization `∑_k g(z+k)`, whose cell integral is `∫ g`. Under `θ ↦ θ + 2πm` the
periodic part is multiplied by `e^{-2πim·z}`, consistent with the fibre problem at the shifted
frequency. There are no constants; only `g₁` (the metric threshold) precedes the data. -/
def AmplitudeIdentificationStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D Nw : ℕ} (H J : ℕ) (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D)
    (η S ηg t₀ Sw ϖ a b : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (g : ℝ) (reg : BlockRegions), CoreScalarPackage K η G v t₀ Sw ϖ reg →
    IsWordPiece K g₁ H J π letters η S ηg ϖ G v g reg a b →
    t₀ ≤ a → a ≤ b → b ≤ t₀ + Sw →
  ∀ (X₀ : Vec 2) (κ : Fin (Nw + 1) → ι → ℕ), IsWordSlots letters κ → (∀ j x, κ j x ≤ J) →
  ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
    (∃ R : ℝ, ∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → planeValue (f x) z = 0) →
    IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ a b v f (fun _ _ _ => 0) u w →
    (∀ (j : Fin (Nw + 1)) (x : ι), ∀ t ∈ Set.Icc a b, ∀ n : ℕ, ∀ β ∈ momentIndices n,
      Integrable (fun y : Vec 2 => (y 0 ^ β.1 * y 1 ^ β.2) • planeValue (u j x t) y)) ∧
    (∀ (j : Fin (Nw + 1)) (x : ι) (e : h x) (θ : Vec 2) (β : ℕ × ℕ), ∃ Dθ : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Set.Icc a b)
        (fibreCoefficients η G v (planeFibreFrequency η θ) (fun _ => 0))
        (fun r z => planeBlochC θ (fun y =>
          (momentWeightLap (G r) β y + ∑ i, v r y i * momentWeightGrad β y i) *
              inner ℝ e (planeValue (u j x r) y) -
            ∑ i, momentWeightGrad β y i * inner ℝ e
              (wordChainPreviousFlux letters X₀ (ϖ * ηg) κ (fun q => w q.1 q.2 r) (j, x) r y i)) z)
        (fun r z => WithLp.toLp 2 fun k => planeBlochC θ (fun y =>
          momentWeight β y * inner ℝ e
              (wordChainPreviousFlux letters X₀ (ϖ * ηg) κ (fun q => w q.1 q.2 r) (j, x) r y k) -
            (∑ i, (G r k i + G r i k) * momentWeightGrad β y i) *
              inner ℝ e (planeValue (u j x r) y)) z)
        Dθ ∧
      ∀ t ∈ Set.Icc a b, cellValue Dθ t =ᵐ[volume.restrict AVenhance.unitCube]
        planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (u j x t) y))) ∧
    ∀ (x : ι) (e : h x) (θ : Vec 2),
      (∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
          (inner ℝ e (planeValue (u (Fin.last Nw) x b) y) : ℂ)) =
        ∫ z in AVenhance.unitCube,
          planeBlochC θ (fun y => inner ℝ e (planeValue (u (Fin.last Nw) x b) y)) z

end AVRegularity.CycleWords.Assembly
end
end
end

section
section
/-! # The level-0 stage data are the Bloch fibre derivatives (statement)

At the start `a` of a piece, the level-0 stage values are the periodic parts
`planeBlochC θ (y^α ⟨e, φ x⟩)`, one per vector `e` of an orthonormal basis of `h x`. Their squared
moduli, summed over the basis, are pointwise on the cell the squared pair of the `θ`-derivatives
`∂_θ^α` of the Bloch sums `blochCos θ (φ x)`, `blochSin θ (φ x)`, which is what `datumJets` (through
`blochFibreDerivNorm`) measures. The identity has no constant and does not depend on the dimension
of `h x`; this is why the constant `Cd` of `WordFibreFactsStatement` can be chosen before the
component spaces. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization

namespace AVRegularity.CycleWords.Assembly

universe u

/-- **The level-0 stage data identity.** For a compactly supported `g : ℝ² → E` and an
orthonormal basis `b` of `E`, at every point `z` of the unit cell,
`∑_e |planeBlochC θ (y^α ⟨b_e, g⟩)(z)|² = ‖∂_θ^α blochCos θ g z‖² + ‖∂_θ^α blochSin θ g z‖²`.

The degenerate cases are included. `α = 0`: `planeBlochC θ ⟨b_e, g⟩ = ⟨b_e, C⟩ - i⟨b_e, S⟩`
with `C, S` the Bloch sums, and Parseval in `E`. `g = 0`: both sides vanish. `E = 0` (`n = 0`):
both sides vanish. `θ = 0`: `blochSin 0 g = 0`, and the identity is Parseval for the
periodization of `y^α g`. There is no constant. -/
def LevelZeroDataStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (g : Vec 2 → E), HasCompactSupport g →
    ∀ (α : ℕ × ℕ) (θ z : Vec 2), z ∈ AVenhance.unitCube →
    ∑ e, ‖planeBlochC θ (fun y => momentWeight α y * inner ℝ (b e) (g y)) z‖ ^ 2 =
      ‖thetaPartial α.1 α.2 (fun θ' => blochCos θ' g z) θ‖ ^ 2 +
        ‖thetaPartial α.1 α.2 (fun θ' => blochSin θ' g z) θ‖ ^ 2

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # Jet-to-value transfer

The stage fluxes of a word chain at one frequency are Bloch parts of moment-weighted jets
`planeBlochC θ (y^β ∂^w h)` of the previous level. Tested against a smooth periodic `φ`, such a
jet is a combination of moment-weighted values `planeBlochC θ (y^{β-a} h)` tested against twisted
derivatives `(∂ - iθ)^{c-a} φ` of the test, where `c` counts the letters of `w`: integrate by parts
on the plane (`integral_phase_mul_eq_cell_planeBlochC` moves between the cell and the plane), one
letter at a time. A letter lands either on the test (twisted derivative `fibreCovDeriv (-θ) k`) or
on the weight (`∂_k y^β = β_k y^{β - e_k}`):

`∫_□ B_θ(y^β ∂^w h) φ = (-1)^n ∑_{a ≤ c} C(c,a) β^{(a)} ∫_□ B_θ(y^{β-a} h) (D_{-θ})^{c-a} φ`,

with `C(c,a) = C(c₀,a₀) C(c₁,a₁)` and the descending factorials `β^{(a)} = β₀^{(a₀)} β₁^{(a₁)}`
(zero when `a_k > β_k`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.CycleWords.Assembly

/-- The letter counts `(#{i : w i = 0}, #{i : w i = 1})` of a word. -/
def wordCount {n : ℕ} (w : DerivativeWord2 n) : ℕ × ℕ :=
  ((Finset.univ.filter fun i => w i = 0).card, (Finset.univ.filter fun i => w i = 1).card)

/-- The twisted derivative `(∂₀ + iθ₀)^{b₀} (∂₁ + iθ₁)^{b₁}`. -/
def fibreCovPow (θ : Vec 2) (b : ℕ × ℕ) (φ : Vec 2 → ℂ) : Vec 2 → ℂ :=
  (fibreCovDeriv θ 0)^[b.1] ((fibreCovDeriv θ 1)^[b.2] φ)

end AVRegularity.CycleWords.Assembly
end
end
end
