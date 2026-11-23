import Box
import Mixture

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace O71
def ballMass : ℝ := (volume ballW).toReal
theorem ballMass_pos : 0 < ballMass := ENNReal.toReal_pos
  (Metric.measure_closedBall_pos volume _ (by norm_num)).ne' (isCompact_closedBall _ _).measure_ne_top

theorem restricted_evidence {n : ℕ} (s : Sample n) {L q : ℝ} (hq : 0 < q) (hL : 0 < L)
    (hbox : ∀ w ∈ box L, radiusSq (scaledChart q w) ≤ 1/9) :
    ENNReal.ofReal (q^11*small^8*L/ballMass) * mixture (boxLaw L) (chartNet q) s ≤ evidence s := by
  let W : Set Param := {w | radiusSq w ≤ 1/9}
  have hW : MeasurableSet W := measurableSet_le radiusSq_continuous.measurable measurable_const
  let F := fun w : Param => likelihood (net w) s
  have hF : Measurable F := by unfold F likelihood ratio eexp net; fun_prop
  have he (w : Space) : (W.indicator F) (physical w) =
      ballW.indicator (fun u => likelihood (prediction u) s) w := by
    have heq : physical w ∈ W ↔ w ∈ ballW := by
      change radiusSq (physical w) ≤ 1/9 ↔ dist w center ≤ 1/3
      rw [physical_radius]; constructor <;> intro hh <;> nlinarith [dist_nonneg (x := w) (y := center)]
    by_cases h : w ∈ ballW
    · rw [indicator_of_mem (heq.mpr h),indicator_of_mem h]
      rfl
    · rw [indicator_of_notMem (mt heq.mp h),indicator_of_notMem h]
  have hp := physical_preserving.lintegral_comp (hF.indicator hW)
  simp_rw [he] at hp
  rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet] at hp
  have ht := scaledChart_factor q hq (W.indicator F) (hF.indicator hW)
  rw [abs_of_pos (pow_pos hq _)] at ht
  have hl : ∫⁻ w in box L, likelihood (chartNet q w) s ≤ ∫⁻ w, W.indicator F (scaledChart q w) := by
    rw [← lintegral_indicator (box_meas L)]
    apply lintegral_mono
    intro w
    by_cases hw : w ∈ box L
    · rw [indicator_of_mem hw]; change _ ≤ W.indicator F (scaledChart q w); rw [indicator_of_mem (show scaledChart q w ∈ W from hbox w hw)]
    · rw [indicator_of_notMem hw]; exact zero_le
  unfold evidence prior ProbabilityTheory.cond
  rw [lintegral_smul_measure,hp,ht]
  unfold mixture boxLaw ProbabilityTheory.cond
  rw [lintegral_smul_measure,smul_eq_mul,smul_eq_mul,box_volume]
  have hmass : ENNReal.ofReal ballMass = volume ballW :=
    ENNReal.ofReal_toReal (isCompact_closedBall _ _).measure_ne_top
  rw [ENNReal.ofReal_div_of_pos ballMass_pos,hmass,
    ENNReal.ofReal_mul (by positivity : 0 ≤ q^11*small^8),
    ENNReal.ofReal_mul (by positivity : 0 ≤ q^11),div_eq_mul_inv]
  calc
    _ = (volume ballW)⁻¹ * (ENNReal.ofReal (q^11) *
        ((ENNReal.ofReal (small^8)*ENNReal.ofReal L) * (ENNReal.ofReal (small^8)*ENNReal.ofReal L)⁻¹ *
          ∫⁻ w in box L, likelihood (chartNet q w) s)) := by ring
    _ ≤ _ := by
      rw [ENNReal.mul_inv_cancel (by positivity) (by finiteness),one_mul]
      gcongr
end O71
