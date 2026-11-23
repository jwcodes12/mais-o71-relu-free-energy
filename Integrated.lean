import PairEstimate
import Mixture
import Strip

noncomputable section
open MeasureTheory Real Filter Set ProbabilityTheory
open scoped ENNReal Topology
namespace O71
theorem measurableChartNet (q : ℝ) : Measurable (chartNet q).uncurry := by
  have hm : Measurable (fun z : Param × ℝ => net z.1 z.2) := by unfold net; fun_prop
  exact hm.comp (((chart_measurable q).comp measurable_fst).prodMk measurable_snd)

def secondBound := exp 99 + 1

theorem box_square_bound (n : ℕ) (q L C F d : ℝ) (hL : 0 < L) (hd : 0 ≤ d)
    (h : ∀ z ∈ box L ×ˢ box L, chartKernel n q z ≤ eexp C ∧
      (d < |coordT z.1-coordT z.2| → chartKernel n q z ≤ eexp F)) :
    (∫⁻ s : Sample n, (mixture (boxLaw L) (chartNet q) s)^2 ∂sampleLaw n) ≤
      ENNReal.ofReal (exp F + exp C * (200*d)) := by
  letI : Fact (0 < L) := ⟨hL⟩
  let ν := boxLaw L
  let bad := {z : Param × Param | |coordT z.1-coordT z.2| ≤ d}
  have hm : MeasurableSet bad := measurableSet_le (by fun_prop) measurable_const
  have hin : ∀ᵐ z ∂ν.prod ν, z ∈ box L ×ˢ box L :=
    (Measure.ae_prod_iff_ae_ae ((box_meas L).prod (box_meas L))).mpr ((ae_cond_mem (μ := volume) (box_meas L)).mono
      (fun _ hu => (ae_cond_mem (μ := volume) (box_meas L)).mono (fun _ hv => ⟨hu,hv⟩)))
  rw [mixture_square _ (measurableChartNet _)]
  change (∫⁻ z, chartKernel n q z ∂ν.prod ν) ≤ _
  have hh : ∀ᵐ z ∂ν.prod ν, chartKernel n q z ≤ eexp F + bad.indicator (fun _ => eexp C) z := by
    filter_upwards [hin] with z hz
    by_cases hb : z ∈ bad
    · rw [indicator_of_mem hb]; exact (h z hz).1.trans le_add_self
    · rw [indicator_of_notMem hb,add_zero]; exact (h z hz).2 (lt_of_not_ge hb)
  refine (lintegral_mono_ae hh).trans ?_
  rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one,lintegral_indicator hm,
    setLIntegral_const,ENNReal.ofReal_add (exp_pos _).le (by positivity),
    ENNReal.ofReal_mul (exp_pos _).le]
  exact add_le_add_right (mul_le_mul_right (box_strip_bound hL hd) _) _

theorem integrated_square {L : ℝ} (hL : 0 < L) :
    ∀ᶠ k in atTop, (∫⁻ s : Sample (sampleSize k),
      (mixture (boxLaw L) (chartNet (scale k)) s)^2 ∂sampleLaw (sampleSize k)) ≤ ENNReal.ofReal secondBound := by
  obtain ⟨C,hC⟩ := pair_bounds hL
  have ht : Tendsto (fun k => exp C * (200*(2*(1+L)*(scale k)^2))) atTop (𝓝 0) := by
    simpa using ((((scale_limit.pow 2).const_mul (2*(1+L))).const_mul 200).const_mul (exp C))
  filter_upwards [hC,ht.eventually_lt tendsto_const_nhds zero_lt_one] with k hk hsmall
  exact (box_square_bound _ _ _ _ _ _ hL (by positivity) hk).trans (ENNReal.ofReal_le_ofReal (by
    unfold secondBound; linarith))
end O71
