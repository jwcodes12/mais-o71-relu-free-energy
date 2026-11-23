import Box

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace O71
theorem box_interval_bound {L : ℝ} (hL : 0 < L) (t d : ℝ) (hd : 0 ≤ d) :
    boxLaw L {w | |t-coordT w| ≤ d} ≤ ENNReal.ofReal (200*d) := by
  let A := Icc (fun _ : Fin 3 => (1:ℝ)) (fun _ => 1+small)
  let T := Icc 1 (1+L) ×ˢ Icc (0:ℝ) 1 ×ˢ Icc (fun _ : Fin 3 => (0:ℝ)) (fun _ => small)
  let P : Set Param := A ×ˢ Icc 0 small ×ˢ Icc (t-d) (t+d) ×ˢ T
  have hs : box L ∩ {w | |t-coordT w| ≤ d} ⊆ P := by
    intro w hw
    have h := abs_le.mp (show |t-coordT w| ≤ d from hw.2)
    exact ⟨hw.1.1,hw.1.2.1,⟨by linarith [h.2],by linarith [h.1]⟩,hw.1.2.2.2⟩
  have hp : volume P = ENNReal.ofReal (small^7)*ENNReal.ofReal (2*d)*ENNReal.ofReal L := by
    simp only [P,A,T,Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Icc_pi,Real.volume_Icc,
      Fin.prod_univ_three,add_sub_cancel_left,sub_zero,show t+d-(t-d) = 2*d by ring,
      ENNReal.ofReal_one,ENNReal.ofReal_pow (by norm_num : 0 ≤ small)]
    ring
  rw [cond_apply (box_meas L)]
  calc
    _ ≤ (volume (box L))⁻¹ * volume P := by gcongr
    _ = _ := by
      rw [box_volume,hp,← ENNReal.ofReal_mul (by positivity : 0 ≤ small^8),← ENNReal.ofReal_inv_of_pos (by positivity),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ small^7),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ small^7*(2*d)),← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp [hL.ne']
      norm_num [small] <;> ring

theorem box_strip_bound {L d : ℝ} (hL : 0 < L) (hd : 0 ≤ d) :
    ((boxLaw L).prod (boxLaw L)) {z | |coordT z.1-coordT z.2| ≤ d} ≤ ENNReal.ofReal (200*d) := by
  letI : Fact (0 < L) := ⟨hL⟩
  rw [Measure.prod_apply (measurableSet_le (by fun_prop) measurable_const)]
  exact (lintegral_mono (μ := boxLaw L) (fun w => box_interval_bound hL (coordT w) d hd)).trans_eq (by simp)
end O71
