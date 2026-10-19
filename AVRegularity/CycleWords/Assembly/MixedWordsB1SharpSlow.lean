-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.TransverseHsProjection

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # Sharp pass: sharp fast decay of the adjoint tests (statement)

The sharp H4 of the word fibre facts needs the adjoint test curves to decay in the test norms `H^{s_k}` at the
rate `π²/8` with a constant independent of `P_e` and `S`. In `L²` this holds for every actual-fast
curve (`revCurve_fast_decay`: the drift is skew). In `H^j` the drift's derivatives cost `P_e`
except on transverse tests in a pulse window, where the drift is a shear. The statement
(`SharpFastDecayStatement`): an actual-fast reversed curve, transverse at its start to the least
window, extended by `D/2` to the right, containing that time (`IsLeastWindow`), if any,
decays in `H^j` at `π²/8` with a constant
independent of `P_e`, in the well-buffered regime `C_b(1 + B_p)P_e^Q e^{-c·buffer} ≤ 1`.

The mechanism:
1. In a window, T1 (c') splits the curve into a decaying transverse part and a local slow part.
   The curve is exactly actual-fast (the pairing with `1 + r` is conserved), and
   `⟨1 + r, ℓ_T⟩ ≈ 1` (`replace_graph`), so the slow coefficient is bounded by the fast part.
2. Quiet stretches: the mean-free part decays in `H^j` at `π²/2`, and fastness bounds
   the mean by the mean-free part.
3. A backward crossing into the previous window: the non-transverse part has crude `P_e^Q` bounds,
  but it has passed a quiet stretch: the left buffer `[lo_q − D, lo_q)` of the window
   just left (`buffer_quiet`), or `(t − D/2, t]` at the start. The surplus `e^{-3π²D/16}` beats
   `P_e^Q/(1+B_p)`, and there are at most `P ≤ B_p/2` crossings. No separation of the windows is
   needed. -/

/-- `p` is the least index of a nondegenerate window (`lo_p ≤ hi_p`) which, extended to the right
by half the buffer, contains `t`: `t ∈ [lo_p, hi_p + D/2]`. The sharp class asks transversality
to this window only; the package does not exclude overlapping windows.

Why this extension:
* With the plain window `[lo_p, hi_p]`, a test at `t` early in the right buffer enters the active
  window backward after less than `D` of quiet time, with no surplus, so the sharp fast decay fails.
* On `[lo_p − D, t] ⊆ [lo_p − D, hi_p + D]` the drift is the shear `ext p` (`ext_agree`). This holds
  whatever other windows overlap.
* Outside every extended window, `(t − D/2, t]` is quiet (`cover`), which gives the surplus.
* Half and not all of the buffer: a later window of the other orientation can be active right
  after `hi_p + D`. At `t ≤ hi_p + D/2` the slow test still has `D/2` of distance to it
  (the sharp slow test, second clause).
* Least and not every window: transversality to two orientations would leave only `0` in the
  sharp class.
* Nondegenerate windows only (`lo ≤ hi`, which `BlockRegions` does not require). A degenerate window is entirely quiet: its enlarged interval `[lo − D, hi + D]` lies
  in its two buffers (`buffer_quiet`). It carries no drift and contains no time, so it imposes
  nothing. Counting it as least would hide a genuine window just behind `t`. -/
def IsLeastWindow (reg : BlockRegions) (p : Fin reg.P) (t : ℝ) : Prop :=
  t ∈ Icc (reg.lo p) (reg.hi p + reg.buffer / 2) ∧ reg.lo p ≤ reg.hi p ∧
    ∀ p' : Fin reg.P, p' < p → reg.lo p' ≤ reg.hi p' →
      t ∉ Icc (reg.lo p') (reg.hi p' + reg.buffer / 2)

/-- **Sharp fast decay of the adjoint tests.**

For `t = s` take `w = w₀` (`C ≥ 1`). For `ξ = 0` one has `r = 0`, fast means mean zero, and the
curve is a heat-type flow: transverse in windows, Fourier-diagonal in quiet stretches. With no
regions (`P = 0`) every time is quiet, and the decay is at `π²/2` with the mean controlled by
fastness. For a single window containing `[s, t]` the first step alone suffices. The remaining case,
`t ∈ (hi_p, hi_p + D/2]` and a non-transverse `u(−t)`, is excluded, since `t` is in the extended
window. If `t ∈ (hi_p + D/2, hi_p + D]` lies in no extended window, then `(hi_p, t]` is quiet, of
length `> D/2`, before the window. The constants `C, C_b, c, Q` depend on `K, j, ρ` only. -/
def SharpFastDecayStatement : Prop :=
  ∀ (K : ScalarConstants) (j : ℕ) (ρ : ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo →
  ∃ (C Cb c : ℝ) (Q : ℕ), 1 ≤ C ∧ 0 < c ∧
  ∀ (η t₀ S ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions) (pkg : CoreScalarPackage K η G v t₀ S ϖ reg),
    0 < η → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    (∀ (i : ℕ) t z, ‖iteratedFDeriv ℝ i (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj i) →
    0 ≤ g → g ≤ K.g0 → IsMetricNearIdentity (fun t _ => G t) g →
  ∀ (ξ : Fin 2 → ℂ) (H : TransverseLocalHyp K η G v ξ), fibreNorm ξ ≤ ρ →
    Cb * (1 + (reg.joins : ℝ)) * peFactor η ^ Q * Real.exp (-c * reg.buffer) ≤ 1 →
  ∀ (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {s t : ℝ}, t₀ ≤ s → s ≤ t →
    t ≤ t₀ + S →
  ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' (-t) (-s) u slice →
    cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) t + cellConstantCLM 1)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0 →
    (∀ p, IsLeastWindow reg p t →
      cellTransverseProjection (reg.orient p) (u (-t)) = u (-t)) →
  ∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u (-t) →
    ∃ w : TorusHk j ℂ, torusHkValueCLM w = u (-s) ∧
      ‖w‖ ≤ C * Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) * ‖w₀‖

/-! # Sharp pass: the sharp slow test (statement)

The slow test `q` of the word fibre facts is the adjoint curve from `1` at `b`, `q(r) = conj u(−r)` for a reversed
curve `u` with `u(−b) = 1`. Its conserved pairing is `⟨1 + r(r), q(r)⟩ = E(r) = e^{∫_r^b λ}`.
Since `cellComplexPair a z = ∫ a z̄`, a constant `c` pairs as `c̄(1 + mean r)`, so `q ≈ Ē·1`, not
`E·1`: the odd Taylor coefficients of `λ` are imaginary, so `Ē − E` is not `O(|ξ|)|E|` (so a statement with error `O(|ξ|)|E|` is false). The sharp blocks need `q(r) = Ē(r)(1 + d(r))` with
`‖d(r)‖_{H^j} ≤ C|ξ|`, the constant independent of `P_e`. In a pulse window `q(r)` must also be
transverse up to the replacement error. Both hold in the well-buffered regime, with `b` quiet
(`SharpSlowTestStatement`). In the word fibre facts the well-buffered regime forces `D_q > 0`, so `b` lies in the
quiet end.

Route (sharp pass and its refinement):
* `1 + d` solves the row equation, forced by `L*1 − λ = O(|ξ|)`. The forcing `θ·v = ξ·(√η v)`
  has jets free of `P_e`, it is transverse in windows (shear drift), and it is constant in quiet
  stretches.
* Equivalently, `q = Eℓ + f`, with the actual row `ℓ ≈ ℓ_T` in windows (`replace_row`) and `f` the
  fast part of `1 − ℓ(b) = O(|ξ|)`, decaying backward (the sharp fast decay, no transversality at the quiet
  `b`).
* Non-transverse parts entering a window have crossed a quiet buffer; the crude evolution inside
  the window costs `P_e^Q`. -/

/-- **The sharp slow test.**

For `r = b` one has `q(b) = 1 = Ē(b)·1`, so the first difference is `0`; `1` is transverse, so
the second is `0`. For `ξ = 0` one has `λ = 0`, `E = 1`, and the adjoint of `1` is `1` (no shift,
mean-zero drift), so both differences vanish. On a quiet stretch the constant mode evolves by its
symbol, and `q(r) − E(r)` comes from the gap between the actual `λ` and the constant-mode symbol,
`O(|ξ|)`. The constants `C, C_b, c, Q` depend on `K, j, ρ` only. -/
def SharpSlowTestStatement : Prop :=
  ∀ (K : ScalarConstants) (j : ℕ) (ρ : ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo →
  ∃ (C Cb c : ℝ) (Q : ℕ), 0 ≤ C ∧ 0 < c ∧
  ∀ (η t₀ S ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions) (pkg : CoreScalarPackage K η G v t₀ S ϖ reg),
    0 < η → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    (∀ (i : ℕ) t z, ‖iteratedFDeriv ℝ i (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj i) →
    0 ≤ g → g ≤ K.g0 → IsMetricNearIdentity (fun t _ => G t) g →
  ∀ (ξ : Fin 2 → ℂ) (H : TransverseLocalHyp K η G v ξ), fibreNorm ξ ≤ ρ →
    Cb * (1 + (reg.joins : ℝ)) * peFactor η ^ Q * Real.exp (-c * reg.buffer) ≤ 1 →
  ∀ (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {a b : ℝ}, t₀ ≤ a → a ≤ b →
    b ≤ t₀ + S → b ∈ reg.quiet →
  ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' (-b) (-a) u slice →
    u (-b) = cellConstantCLM 1 →
  ∀ r ∈ Icc a b,
    (∃ w : TorusHk j ℂ, torusHkValueCLM w =
        cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-r)) -
          cellConstantCLM (star (Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ))) ∧
      ‖w‖ ≤ C * fibreNorm ξ * ‖Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ)‖) ∧
    ∀ p, IsLeastWindow reg p r →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w =
          cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-r)) -
            cellTransverseProjection (reg.orient p)
              (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-r))) ∧
        ‖w‖ ≤ C * peFactor η ^ Q * Real.exp (-c * reg.buffer) * fibreNorm ξ *
          ‖Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ)‖

end AVRegularity.CycleWords.Assembly
end
