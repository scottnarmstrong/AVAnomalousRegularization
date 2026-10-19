-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.OcNextStream
import AVenhance.Infra.Flow.JointSmoothFromFixedStart
import AVenhance.Statements.FlowDefs.FlowIsFlow
public import AVenhance.Infra.Flow.PeriodicSmooth
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.Flow.CurveUniqueness
import AVenhance.Infra.Flow.Laws
import AVenhance.Infra.Flow.SmoothField

section
@[expose] public section
namespace AVRegularity.Construction.Stream

/-! Arithmetic facts needed for the integer space-time shifts in the stream
recursion. -/

theorem ocEpsilon_pos {q : ℝ} {Λ n : ℕ} (hΛ : 1 ≤ Λ) :
    0 < ocEpsilon q Λ n := by
  by_cases hn : n = 0
  · simp [ocEpsilon, hn]
  · simp only [ocEpsilon, hn]
    apply inv_pos.mpr
    have hbase : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
    have hpow : 0 < (Λ : ℝ) ^ (q ^ n / (q - 1)) :=
      Real.rpow_pos_of_pos hbase _
    exact_mod_cast (Nat.ceil_pos.mpr hpow)

theorem ocEpsilon_inv_eq_nat {q : ℝ} {Λ m : ℕ} (hm : 1 ≤ m) :
    (ocEpsilon q Λ m)⁻¹ =
      (⌈(Λ : ℝ) ^ (q ^ m / (q - 1))⌉₊ : ℝ) := by
  have hm0 : m ≠ 0 := by omega
  simp [ocEpsilon, hm0]

theorem ocTauPP_pos {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) :
    0 < ocTauPP α q Λ m := by
  unfold ocTauPP
  apply div_pos
  · positivity
  · apply Nat.cast_pos.mpr
    apply Nat.ceil_pos.mpr
    exact Real.rpow_pos_of_pos
      (ocEpsilon_pos (q := q) (Λ := Λ) (n := m - 1) hΛ) _

theorem ocTauPP_reciprocal_exact {α q : ℝ} {Λ m : ℕ}
    (hΛ : 1 ≤ Λ) :
    1 / ocTauPP α q Λ m =
      (2 : ℝ) ^ (25 : ℕ) *
        (⌈ocEpsilon q Λ (m - 1) ^ (-(2 - (1 + α) + 2 * ocDelta α q))⌉₊ : ℝ) := by
  let C : ℕ :=
    ⌈ocEpsilon q Λ (m - 1) ^ (-(2 - (1 + α) + 2 * ocDelta α q))⌉₊
  have hC : 0 < C := by
    dsimp [C]
    apply Nat.ceil_pos.mpr
    exact Real.rpow_pos_of_pos
      (ocEpsilon_pos (q := q) (Λ := Λ) (n := m - 1) hΛ) _
  have hCne : (C : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have hpow : (2 : ℝ) ^ (-25 : ℤ) = ((2 : ℝ) ^ (25 : ℕ))⁻¹ := by norm_num
  rw [ocTauPP, hpow]
  field_simp [hCne]

theorem ocTauPP_reciprocal_multiple_four {α q : ℝ} {Λ m : ℕ}
    (hΛ : 1 ≤ Λ) :
    ∃ n : ℕ, 1 / ocTauPP α q Λ m = (4 * n : ℕ) := by
  refine ⟨2 ^ 23 *
    ⌈ocEpsilon q Λ (m - 1) ^ (-(2 - (1 + α) + 2 * ocDelta α q))⌉₊, ?_⟩
  rw [ocTauPP_reciprocal_exact hΛ]
  push_cast
  norm_num
  ring

theorem ocTau_pos {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) :
    0 < ocTau α q Λ m := by
  have hL : 0 < (ocL α q Λ m : ℝ) := by
    have hLn : 0 < ocL α q Λ m := by
      unfold ocL
      omega
    exact_mod_cast hLn
  unfold ocTau
  apply div_pos (ocTauPP_pos hΛ)
  exact pow_pos hL _

theorem ocTau_reciprocal_multiple_four {α q : ℝ} {Λ m : ℕ}
    (hΛ : 1 ≤ Λ) :
    ∃ n : ℕ, 1 / ocTau α q Λ m = (4 * n : ℕ) := by
  let L := ocL α q Λ m
  let C := ⌈ocEpsilon q Λ (m - 1) ^
    (-(2 - (1 + α) + 2 * ocDelta α q))⌉₊
  have hLpos : 0 < L := by
    dsimp [L, ocL]
    omega
  have hτPP := ocTauPP_pos (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hrecipPP := ocTauPP_reciprocal_exact (α := α) (q := q)
    (Λ := Λ) (m := m) hΛ
  refine ⟨L ^ 2 * (2 ^ 23 * C), ?_⟩
  have hfactor : 1 / ocTau α q Λ m =
      (L : ℝ) ^ 2 * (1 / ocTauPP α q Λ m) := by
    rw [ocTau]
    field_simp [ne_of_gt hτPP]
    dsimp [L]
  rw [hfactor, hrecipPP]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  dsimp [L, C]
  norm_num
  ring

end AVRegularity.Construction.Stream
end
end

section
@[expose] public section
noncomputable section
open Homogenization AVenhance Filter Topology
open scoped ContDiff
namespace AVRegularity.Construction.Stream

/-! Smoothness and integer space-time periodicity of one OC stream step. -/

def ocNextStreamTerm (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (t : ℝ) (x : Vec 2) (k : ℤ) : ℝ :=
  slowEnvelope α q Λ m (ocLabel α q Λ m k) t *
    ζ ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m) *
    ocShear α q Λ m k
      (flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz t x
        ((ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m))

theorem ocShear_index_periodic (α q : ℝ) (Λ m : ℕ) {K : ℤ}
    (hK : K % 4 = 0) (k : ℤ) (y : Vec 2) :
    ocShear α q Λ m (k + K) y = ocShear α q Λ m k y := by
  have h1 : ((k + K) % 4 = 1) = (k % 4 = 1) := propext (by omega)
  have h3 : ((k + K) % 4 = 3) = (k % 4 = 3) := propext (by omega)
  simp [ocShear, psi0, h1, h3]

theorem ocShear_lattice_periodic (α q : ℝ) {Λ m : ℕ}
    (hm : 1 ≤ m) (k : ℤ) (y : Vec 2) (j : Fin 2 → ℤ) :
    ocShear α q Λ m k (y + latticeShift j) = ocShear α q Λ m k y := by
  let E : ℕ := ⌈(Λ : ℝ) ^ (q ^ m / (q - 1))⌉₊
  have hE : (ocEpsilon q Λ m)⁻¹ = (E : ℝ) := by
    simpa [E] using ocEpsilon_inv_eq_nat (q := q) hm
  have hscaled (i : Fin 2) :
      ((ocEpsilon q Λ m)⁻¹ • (y + latticeShift j)) i =
        ((ocEpsilon q Λ m)⁻¹ • y) i + (((E : ℤ) * j i : ℤ) : ℝ) := by
    simp only [Pi.smul_apply, Pi.add_apply, latticeShift]
    rw [hE]
    push_cast
    ring
  have hsin (i : Fin 2) :
      Real.sin (2 * Real.pi *
        (((ocEpsilon q Λ m)⁻¹ • (y + latticeShift j)) i)) =
      Real.sin (2 * Real.pi * (((ocEpsilon q Λ m)⁻¹ • y) i)) := by
    rw [hscaled i]
    have harg :
        2 * Real.pi * (((ocEpsilon q Λ m)⁻¹ • y) i +
          (((E : ℤ) * j i : ℤ) : ℝ)) =
        2 * Real.pi * (((ocEpsilon q Λ m)⁻¹ • y) i) +
          ((E : ℤ) * j i : ℤ) * (2 * Real.pi) := by
      push_cast
      ring
    rw [harg, Real.sin_add_int_mul_two_pi]
  have hcore :
      psi0 k ((ocEpsilon q Λ m)⁻¹ • (y + latticeShift j)) =
      psi0 k ((ocEpsilon q Λ m)⁻¹ • y) := by
    unfold psi0
    by_cases h1 : k % 4 = 1
    · simp [h1]
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] using hsin 0
    · by_cases h3 : k % 4 = 3
      · simp [h3]
        simpa only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] using hsin 1
      · simp [h1, h3]
  unfold ocShear
  rw [hcore]

theorem ocLabel_add_time_shift (α q : ℝ) (Λ m : ℕ) (k K J : ℤ)
    (hΛ : 1 ≤ Λ)
    (hKτ : (K : ℝ) * ocTau α q Λ m = (J : ℝ) * ocTauPP α q Λ m) :
    ocLabel α q Λ m (k + K) = ocLabel α q Λ m k + J := by
  have hτPP : 0 < ocTauPP α q Λ m := by
    exact ocTauPP_pos (Λ := Λ) (m := m) hΛ
  have harg :
      (((k + K : ℤ) : ℝ) * ocTau α q Λ m +
        (ocTauPP α q Λ m - ocTau α q Λ m) / 2) / ocTauPP α q Λ m =
      (((k : ℝ) * ocTau α q Λ m +
        (ocTauPP α q Λ m - ocTau α q Λ m) / 2) / ocTauPP α q Λ m) + J := by
    rw [Int.cast_add, add_mul, hKτ]
    field_simp [ne_of_gt hτPP]
    ring
  unfold ocLabel
  rw [harg, Int.floor_add_intCast]

theorem ocZeta_add_time_shift (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ) (k K : ℤ)
    (t N : ℝ) (hKτ : (K : ℝ) * ocTau α q Λ m = N) :
    ζ ((t + N - (k + K : ℤ) * ocTau α q Λ m) / ocTau α q Λ m) =
      ζ ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m) := by
  congr 1
  rw [Int.cast_add, add_mul, hKτ]
  ring

theorem ocSlowEnvelope_add_time_shift (α q : ℝ) (Λ m : ℕ) (l J : ℤ)
    (t N : ℝ) (hJPP : (J : ℝ) * ocTauPP α q Λ m = N) :
    slowEnvelope α q Λ m (l + J) (t + N) =
      slowEnvelope α q Λ m l t := by
  unfold slowEnvelope
  have hleft :
      (t + N - (((l + J : ℤ) : ℝ) - 1 / 2) * ocTauPP α q Λ m -
        ocTauP α q Λ m) / ocTauP α q Λ m =
      (t - ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m -
        ocTauP α q Λ m) / ocTauP α q Λ m := by
    rw [Int.cast_add]
    have hmul : ((l : ℝ) + (J : ℝ) - 1 / 2) * ocTauPP α q Λ m =
        ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m + N := by
      calc
        ((l : ℝ) + (J : ℝ) - 1 / 2) * ocTauPP α q Λ m =
            ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m +
              (J : ℝ) * ocTauPP α q Λ m := by ring
        _ = _ := by rw [hJPP]
    rw [hmul]
    ring
  have hright :
      ((((l + J : ℤ) : ℝ) + 1 / 2) * ocTauPP α q Λ m -
        ocTauP α q Λ m - (t + N)) / ocTauP α q Λ m =
      (((l : ℝ) + 1 / 2) * ocTauPP α q Λ m -
        ocTauP α q Λ m - t) / ocTauP α q Λ m := by
    rw [Int.cast_add]
    have hmul : ((l : ℝ) + (J : ℝ) + 1 / 2) * ocTauPP α q Λ m =
        ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m + N := by
      calc
        ((l : ℝ) + (J : ℝ) + 1 / 2) * ocTauPP α q Λ m =
            ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m +
              (J : ℝ) * ocTauPP α q Λ m := by ring
        _ = _ := by rw [hJPP]
    rw [hmul]
    ring
  rw [hleft, hright]

theorem flow_integer_time_shift {b : ℝ → Vec 2 → Vec 2}
    (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    (N : ℤ) (x : Vec 2) (s t : ℝ) :
    X (t + (N : ℝ)) x (s + (N : ℝ)) = X t x s := by
  rcases hL with ⟨L, hL⟩
  have htime (r : ℝ) (y : Vec 2) : b (r + (N : ℝ)) y = b r y := by
    have h := hb.periodic N (fun _ => 0) r y
    have hz : latticeShift (fun _ : Fin 2 => (0 : ℤ)) = (0 : Vec 2) := by
      ext i
      simp [latticeShift]
    rw [hz, add_zero] at h
    exact h
  have hshift (r : ℝ) : HasDerivAt
      (fun u => X (u + (N : ℝ)) x (s + (N : ℝ)))
      (b r (X (r + (N : ℝ)) x (s + (N : ℝ)))) r := by
    simpa only [Function.comp_def, htime r (X (r + (N : ℝ)) x (s + (N : ℝ)))] using
      (hX.2 x (s + (N : ℝ)) (r + (N : ℝ))).comp_add_const r (N : ℝ)
  have hstart : X (s + (N : ℝ)) x (s + (N : ℝ)) = X s x s := by
    rw [hX.1, hX.1]
  have hcurves := Infra.Flow.integralCurve_unique b hL hshift
    (fun r => hX.2 x s r) hstart
  exact congrFun hcurves t

theorem ocNextStreamTerm_contDiff (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) (m : ℕ) (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (k : ℤ) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
      ocNextStreamTerm α q Λ ζ m φ hφ p.1 p.2 k) := by
  have hb : Infra.Flow.SmoothPeriodicField (streamVel φ) :=
    Infra.Construction.smoothPeriodic_streamVel hφ
  have hX : IsFlow (streamVel φ)
      (flow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz) :=
    flow_isFlow _ _ _
  let start : ℝ := (ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m
  have hflow : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
      flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz p.1 p.2 start) := by
    have hjoint := Infra.Flow.flow_inverse_joint_contDiff_infty hb hX
    have hmap : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (p.1, p.2, start)) := by
      fun_prop
    have hcomp := hjoint.comp hmap
    simpa only [Function.comp_def, flowInv, start] using hcomp
  have hshear : ContDiff ℝ ∞ (ocShear α q Λ m k) := by
    unfold ocShear
    have hinner : ContDiff ℝ ∞
        (fun y : Vec 2 => psi0 k ((ocEpsilon q Λ m)⁻¹ • y)) := by
      unfold psi0
      split_ifs <;> fun_prop
    fun_prop
  have hshearFlow : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
      ocShear α q Λ m k
        (flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz
          p.1 p.2 start)) := hshear.comp hflow
  have hslow : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
      slowEnvelope α q Λ m (ocLabel α q Λ m k) p.1) := by
    unfold slowEnvelope
    fun_prop
  have hfast : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
      ζ ((p.1 - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m)) :=
    hζ.1.comp (by fun_prop)
  change ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
    slowEnvelope α q Λ m (ocLabel α q Λ m k) p.1 *
      ζ ((p.1 - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m) *
      ocShear α q Λ m k
        (flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz p.1 p.2 start))
  simpa [mul_assoc] using hslow.mul (hfast.mul hshearFlow)

theorem ocNextStreamTerm_nonzero_distance (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) (hΛ : 1 ≤ Λ) (m : ℕ) (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (t : ℝ) (x : Vec 2) (k : ℤ)
    (hne : ocNextStreamTerm α q Λ ζ m φ hφ t x k ≠ 0) :
    |t - (k : ℝ) * ocTau α q Λ m| ≤ (2 / 3 : ℝ) * ocTau α q Λ m := by
  have hτ : 0 < ocTau α q Λ m := ocTau_pos (Λ := Λ) (m := m) hΛ
  have hz : ζ ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m) ≠ 0 := by
    intro hz
    apply hne
    simp [ocNextStreamTerm, hz]
  have hargmem :
      (t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m ∈ tsupport ζ :=
    (subset_tsupport ζ) (Function.mem_support.mpr hz)
  have harg := hζ.2.2.1 hargmem
  have habs :
      |(t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m| ≤ 2 / 3 :=
    abs_le.mpr ⟨le_of_lt harg.1, le_of_lt harg.2⟩
  have hdiv :
      |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m ≤ 2 / 3 := by
    simpa [abs_div, abs_of_pos hτ] using habs
  rw [div_le_iff₀ hτ] at hdiv
  exact hdiv

theorem ocNextStreamTerm_locally_finite_sum (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) (hΛ : 1 ≤ Λ) (m : ℕ) (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (p : ℝ × Vec 2) :
    ∃ S : Finset ℤ, ∀ᶠ q' : ℝ × Vec 2 in 𝓝 p,
      (∑' k : ℤ, ocNextStreamTerm α q Λ ζ m φ hφ q'.1 q'.2 k) =
        ∑ k ∈ S, ocNextStreamTerm α q Λ ζ m φ hφ q'.1 q'.2 k := by
  let τ := ocTau α q Λ m
  have hτ : 0 < τ := by
    dsimp [τ]
    exact ocTau_pos (Λ := Λ) (m := m) hΛ
  let S : Finset ℤ := Finset.Icc (⌊(p.1 - 1) / τ⌋ - 1)
    (⌈(p.1 + 1) / τ⌉ + 1)
  refine ⟨S, ?_⟩
  have hopen : Set.Ioo (p.1 - 1) (p.1 + 1) ∈ 𝓝 p.1 :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have htime : ∀ᶠ q' : ℝ × Vec 2 in 𝓝 p,
      q'.1 ∈ Set.Icc (p.1 - 1) (p.1 + 1) := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hopen] with q' hq'
    exact ⟨le_of_lt hq'.1, le_of_lt hq'.2⟩
  filter_upwards [htime] with q' hq'
  apply tsum_eq_sum
  intro k hk
  have hzero : ocNextStreamTerm α q Λ ζ m φ hφ q'.1 q'.2 k = 0 := by
    by_contra hne
    have hdist := ocNextStreamTerm_nonzero_distance α q Λ ζ hζ hΛ m φ hφ
      q'.1 q'.2 k hne
    have habs := abs_le.mp hdist
    have hklower : p.1 - 1 - (2 / 3 : ℝ) * τ ≤ (k : ℝ) * τ := by
      nlinarith [hq'.1, habs.2]
    have hkupper : (k : ℝ) * τ ≤ p.1 + 1 + (2 / 3 : ℝ) * τ := by
      nlinarith [hq'.2, habs.1]
    have hloForm : ((p.1 - 1) - (2 / 3 : ℝ) * τ) / τ =
        (p.1 - 1) / τ - 2 / 3 := by
      field_simp [ne_of_gt hτ]
    have hhiForm : ((p.1 + 1) + (2 / 3 : ℝ) * τ) / τ =
        (p.1 + 1) / τ + 2 / 3 := by
      field_simp [ne_of_gt hτ]
    have hlo : ((p.1 - 1) / τ) - 2 / 3 ≤ (k : ℝ) := by
      rw [← hloForm]
      exact (div_le_iff₀ hτ).2 hklower
    have hhi : (k : ℝ) ≤ ((p.1 + 1) / τ) + 2 / 3 := by
      rw [← hhiForm]
      exact (le_div_iff₀ hτ).2 hkupper
    have hfloor : (⌊(p.1 - 1) / τ⌋ : ℝ) ≤ (p.1 - 1) / τ := Int.floor_le _
    have hceil : (p.1 + 1) / τ ≤ (⌈(p.1 + 1) / τ⌉ : ℝ) := Int.le_ceil _
    have hklo : ((⌊(p.1 - 1) / τ⌋ - 1 : ℤ) : ℝ) ≤ (k : ℝ) := by
      simp only [Int.cast_sub, Int.cast_one]
      linarith
    have hkhi : (k : ℝ) ≤ ((⌈(p.1 + 1) / τ⌉ + 1 : ℤ) : ℝ) := by
      simp only [Int.cast_add, Int.cast_one]
      linarith
    have hklo' : ⌊(p.1 - 1) / τ⌋ - 1 ≤ k := by exact_mod_cast hklo
    have hkhi' : k ≤ ⌈(p.1 + 1) / τ⌉ + 1 := by exact_mod_cast hkhi
    have hmem : k ∈ S := by
      simp only [S, Finset.mem_Icc]
      exact ⟨hklo', hkhi'⟩
    exact (hk hmem).elim
  exact hzero

theorem ocNextStream_smooth (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) (hΛ : 1 ≤ Λ) (m : ℕ) (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) :
    ContDiff ℝ ∞ (Function.uncurry (ocNextStream α q Λ ζ m φ hφ)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  obtain ⟨S, hS⟩ := ocNextStreamTerm_locally_finite_sum α q Λ ζ hζ hΛ m φ hφ p
  have hsum : ContDiff ℝ ∞
      (fun q' : ℝ × Vec 2 =>
        ∑ k ∈ S, ocNextStreamTerm α q Λ ζ m φ hφ q'.1 q'.2 k) := by
    apply ContDiff.sum
    intro k hk
    exact ocNextStreamTerm_contDiff α q Λ ζ hζ m φ hφ k
  have hfinite : ContDiff ℝ ∞
      (fun q' : ℝ × Vec 2 => φ q'.1 q'.2 +
        ∑ k ∈ S, ocNextStreamTerm α q Λ ζ m φ hφ q'.1 q'.2 k) :=
    hφ.1.add hsum
  have heq : (Function.uncurry (ocNextStream α q Λ ζ m φ hφ)) =ᶠ[𝓝 p]
      (fun q' : ℝ × Vec 2 => φ q'.1 q'.2 +
        ∑ k ∈ S, ocNextStreamTerm α q Λ ζ m φ hφ q'.1 q'.2 k) := by
    filter_upwards [hS] with q' hq'
    change φ q'.1 q'.2 +
        ∑' k : ℤ, ocNextStreamTerm α q Λ ζ m φ hφ q'.1 q'.2 k = _
    rw [hq']
  exact hfinite.contDiffAt.congr_of_eventuallyEq heq

theorem ocNextStream_isAdmissible (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) (hΛ : 1 ≤ Λ) (m : ℕ) (hm : 1 ≤ m)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) :
    IsAdmissibleStream (ocNextStream α q Λ ζ m φ hφ) := by
  refine ⟨?_, ?_⟩
  · exact ocNextStream_smooth α q Λ ζ hζ hΛ m φ hφ
  · intro N j t x
    have hb := Infra.Construction.smoothPeriodic_streamVel hφ
    rcases Infra.Flow.exists_global_spatial_lipschitz hb with ⟨Lflow, _, hLflow⟩
    have hL : ∃ L : ℝ, ∀ r y z,
        ‖streamVel φ r y - streamVel φ r z‖ ≤ L * ‖y - z‖ :=
      ⟨Lflow, hLflow⟩
    have hX : IsFlow (streamVel φ)
        (flow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz) :=
      flow_isFlow _ _ _
    have hspace (r : ℝ) : IsZ2Periodic (streamVel φ r) := by
      intro z y
      have hp := hb.periodic 0 z r y
      simpa using hp
    obtain ⟨qτ, hqτ⟩ := ocTau_reciprocal_multiple_four (Λ := Λ) (m := m) hΛ
    obtain ⟨qPP, hqPP⟩ :=
      ocTauPP_reciprocal_multiple_four (Λ := Λ) (m := m) hΛ
    let K : ℤ := N * (4 * (qτ : ℤ))
    let J : ℤ := N * (4 * (qPP : ℤ))
    have hτ : 0 < ocTau α q Λ m := ocTau_pos (Λ := Λ) (m := m) hΛ
    have hτPP : 0 < ocTauPP α q Λ m := ocTauPP_pos (Λ := Λ) (m := m) hΛ
    have hτrecip : (ocTau α q Λ m)⁻¹ = ((4 * qτ : ℕ) : ℝ) := by
      simpa [one_div] using hqτ
    have hτPPrec : (ocTauPP α q Λ m)⁻¹ = ((4 * qPP : ℕ) : ℝ) := by
      simpa [one_div] using hqPP
    have hτunit : ocTau α q Λ m * ((4 * qτ : ℕ) : ℝ) = 1 := by
      rw [← hτrecip]
      exact mul_inv_cancel₀ (ne_of_gt hτ)
    have hτPPunit : ocTauPP α q Λ m * ((4 * qPP : ℕ) : ℝ) = 1 := by
      rw [← hτPPrec]
      exact mul_inv_cancel₀ (ne_of_gt hτPP)
    have hτunit' : ocTau α q Λ m * (4 * (qτ : ℝ)) = 1 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hτunit
    have hτPPunit' : ocTauPP α q Λ m * (4 * (qPP : ℝ)) = 1 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hτPPunit
    have hKtime : (K : ℝ) * ocTau α q Λ m = (N : ℝ) := by
      dsimp [K]
      push_cast
      calc
        (N : ℝ) * (4 * (qτ : ℝ)) * ocTau α q Λ m =
            (N : ℝ) * (ocTau α q Λ m * (4 * (qτ : ℝ))) := by ring
        _ = (N : ℝ) := by rw [hτunit', mul_one]
    have hJtime : (J : ℝ) * ocTauPP α q Λ m = (N : ℝ) := by
      dsimp [J]
      push_cast
      calc
        (N : ℝ) * (4 * (qPP : ℝ)) * ocTauPP α q Λ m =
            (N : ℝ) * (ocTauPP α q Λ m * (4 * (qPP : ℝ))) := by ring
        _ = (N : ℝ) := by rw [hτPPunit', mul_one]
    have hKmod : K % 4 = 0 := by
      have hfour : (4 * (qτ : ℤ)) % 4 = 0 := by omega
      dsimp [K]
      rw [Int.mul_emod, hfour]
      simp
    have hidx (k : ℤ) :
        ocLabel α q Λ m (k + K) = ocLabel α q Λ m k + J := by
      apply ocLabel_add_time_shift α q Λ m k K J hΛ
      calc
        (K : ℝ) * ocTau α q Λ m = (N : ℝ) := hKtime
        _ = (J : ℝ) * ocTauPP α q Λ m := hJtime.symm
    have hflowShift (r : ℝ) (y : Vec 2) (s : ℝ) :
        flow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz
          (r + (N : ℝ)) y (s + (N : ℝ)) =
        flow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz r y s :=
      flow_integer_time_shift hb hX hL N y s r
    have hterm (k : ℤ) :
        ocNextStreamTerm α q Λ ζ m φ hφ
          (t + (N : ℝ)) (x + latticeShift j) (k + K) =
        ocNextStreamTerm α q Λ ζ m φ hφ t x k := by
      have hInv :
          flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz
              (t + (N : ℝ)) (x + latticeShift j)
              (((ocLabel α q Λ m k + J : ℤ) : ℝ) * ocTauPP α q Λ m) =
            flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz t x
              ((ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m) + latticeShift j := by
        change flow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz
            (((ocLabel α q Λ m k + J : ℤ) : ℝ) * ocTauPP α q Λ m)
            (x + latticeShift j) (t + (N : ℝ)) = _
        have hstart :
            ((ocLabel α q Λ m k + J : ℤ) : ℝ) * ocTauPP α q Λ m =
              (ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m + (N : ℝ) := by
          rw [Int.cast_add, add_mul, hJtime]
        rw [hstart, hflowShift]
        exact Infra.Flow.flow_lattice_equivariant (streamVel φ) hL hspace hX
          x t ((ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m) j
      unfold ocNextStreamTerm
      rw [hidx k]
      rw [ocSlowEnvelope_add_time_shift α q Λ m (ocLabel α q Λ m k) J
        t (N : ℝ) hJtime]
      rw [ocZeta_add_time_shift α q Λ m ζ k K t (N : ℝ) hKtime]
      rw [ocShear_index_periodic α q Λ m hKmod k]
      rw [hInv, ocShear_lattice_periodic α q hm k _ j]
    have hsum :
        (∑' k : ℤ, ocNextStreamTerm α q Λ ζ m φ hφ
          (t + (N : ℝ)) (x + latticeShift j) k) =
        ∑' k : ℤ, ocNextStreamTerm α q Λ ζ m φ hφ t x k := by
      rw [← (Equiv.addRight K).tsum_eq]
      congr 1
      funext k
      exact hterm k
    change (φ (t + (N : ℝ)) (x + latticeShift j) +
        ∑' k : ℤ, ocNextStreamTerm α q Λ ζ m φ hφ
          (t + (N : ℝ)) (x + latticeShift j) k) =
      (φ t x + ∑' k : ℤ, ocNextStreamTerm α q Λ ζ m φ hφ t x k)
    rw [hφ.2 N j t x, hsum]

end AVRegularity.Construction.Stream
end
end
end
